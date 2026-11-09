-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_lemma_2_6
-- name    : ParityDegreeDepth.Main.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:49.533796+00:00
-- url     : https://prove2.me/theorems/cacef0b8-d197-400b-8300-97fb61a6db61
-- title:
--   Lemma 2.6 — quadratic spectrum and tree depth
-- statement:
--   Let $p:\mathbb F_2^n\to\mathbb F_2$ have degree at most two and let its polar form $\beta_p(u,v)=p(u+v)+p(u)+p(v)+p(0)$ have rank $2r$. For $f=(-1)^p$,
--   $$s(f)=2^{2r},\qquad |\widehat f(\xi)|\in\{0,2^{-r}\}\ \text{for every }\xi,\qquad\|\widehat f\|_1=2^r,\qquad D_\oplus(f)\le r+1.$$
--
--   This supplies both the complete flat-spectrum statement and the terminal tree bound, including polar rank zero.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
--   - encoding: the quadratic polar form and coefficient magnitude 2^(-r) → the second finite difference at zero on standard basis vectors, and an integer exponent -(r : ℤ); reason: the polar identity is exact for degree at most two, including constants, and no natural exponent is truncated
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Lemma 2.6, PDF page 6 / printed page 5.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main

private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private def phase {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (x : Vec n (ZMod 2)) : ℝ :=
  (-1 : ℝ) ^ (p x).val

private def spectralNorm {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℝ :=
  ∑ a, |QAlgorithms.boolFourier f a|

private def sparsity {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℕ :=
  (Finset.univ.filter fun a => QAlgorithms.boolFourier f a ≠ 0).card

private def coefficient {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
  then 1 else 0

private def anfDegree {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) : WithBot ℕ :=
  Finset.univ.sup fun S : Finset (Fin n) =>
    if coefficient p S = 0 then ⊥ else (S.card : WithBot ℕ)

private inductive ParityTree (n : ℕ) where
  | leaf (b : Bool)
  | query (a : Vec n (ZMod 2)) (ha : a ≠ 0) (zero one : ParityTree n)

private def treeDepth {n : ℕ} : ParityTree n → ℕ
  | .leaf _ => 0
  | .query _ _ l r => 1 + max (treeDepth l) (treeDepth r)

private def treeEval {n : ℕ} : ParityTree n → Vec n (ZMod 2) → ℝ
  | .leaf b, _ => if b then -1 else 1
  | .query a _ l r, x => if ∑ i, a i * x i = 0 then treeEval l x else treeEval r x

private def parityDepth {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℕ :=
  sInf {k | ∃ t : ParityTree n, treeDepth t = k ∧ ∀ x, treeEval t x = f x}

private def delta {n : ℕ} (h : Vec n (ZMod 2)) (p : Vec n (ZMod 2) → ZMod 2)
    (x : Vec n (ZMod 2)) : ZMod 2 := p (x + h) + p x

private def differences {n k : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (h : Fin k → Vec n (ZMod 2)) : Vec n (ZMod 2) → ZMod 2 :=
  (List.ofFn h).foldl (fun q v => delta v q) p

private abbrev Form (F : Type) (n d : ℕ) := (Fin d → Vec n F) → F

private def topForm {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (d : ℕ) : Form (ZMod 2) n d :=
  fun h => differences p h 0

private def contraction {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (h : Fin (d - 2) → Vec n F) : Matrix (Fin n) (Fin n) F :=
  fun i j => T (fun s => if hs : s.val < d - 2 then h ⟨s.val, hs⟩
    else if s.val = d - 2 then Pi.single i 1 else Pi.single j 1)


/-- lemma 2 6; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem lemma_2_6 {n r : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hp : anfDegree p ≤ (2 : WithBot ℕ))
    (hr : (contraction (topForm p 2) (fun i => Fin.elim0 i)).rank = 2 * r) :
    sparsity (phase p) = 2 ^ (2 * r) ∧
    (∀ ξ, |QAlgorithms.boolFourier (phase p) ξ| = 0 ∨
      |QAlgorithms.boolFourier (phase p) ξ| = (2 : ℝ) ^ (-(r : ℤ))) ∧
    spectralNorm (phase p) = (2 : ℝ) ^ r ∧ parityDepth (phase p) ≤ r + 1 := by sorry

end ParityDegreeDepth.Main
