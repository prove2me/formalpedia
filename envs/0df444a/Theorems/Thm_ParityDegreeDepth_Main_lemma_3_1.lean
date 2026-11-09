-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_lemma_3_1
-- name    : ParityDegreeDepth.Main.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:03.620682+00:00
-- url     : https://prove2.me/theorems/5060d68a-0b18-43ed-b349-3cae4ce93f83
-- title:
--   Lemma 3.1 — recursion over degree
-- statement:
--   Let $p:\mathbb F_2^n\to\mathbb F_2$ have exact degree $d\ge2$. Suppose $\Gamma(j)\ge0$ for $2\le j\le d$. For every degree-$j$ affine restriction $q$ of $p$ with $3\le j\le d$, assume $c(\Delta^j q)\le\Gamma(j)$; for every degree-two restriction assume $D_\oplus((-1)^q)\le1+\Gamma(2)$. Then
--   $$D_\oplus((-1)^p)\le1+\sum_{j=2}^d\Gamma(j).$$
--   Here $c(T)$ is the least codimension of a subspace on which $T$ vanishes in all slots. Restrictions range over every affine coordinate injection in every dimension.
--
--   The statement expresses the total cost of the degree recursion using the same cost schedule on every branch.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
--   - encoding: all degree-j affine restrictions with j ≥ 3 → all affine coordinate injections with 3 ≤ j ≤ d; reason: restrictions cannot increase ANF degree, so j > d supplies no additional source instance
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Lemma 3.1, PDF page 6 / printed page 5.

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

private def coefficient {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
  then 1 else 0

private def anfDegree {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) : WithBot ℕ :=
  Finset.univ.sup fun S : Finset (Fin n) =>
    if coefficient p S = 0 then ⊥ else (S.card : WithBot ℕ)

private def affineMap {m n : ℕ} (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2))
    (a : Vec n (ZMod 2)) (y : Vec m (ZMod 2)) : Vec n (ZMod 2) := a + B y

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

private def Vanishes {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (U : Submodule F (Vec n F)) : Prop := ∀ x, (∀ i, x i ∈ U) → T x = 0

private def vanishingCodim {n d : ℕ} (T : Form (ZMod 2) n d) : ℕ :=
  sInf {r | ∃ U : Submodule (ZMod 2) (Vec n (ZMod 2)),
    n - Module.finrank (ZMod 2) U = r ∧ Vanishes T U}


/-- lemma 3 1; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem lemma_3_1 {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hd : 2 ≤ d) (hp : anfDegree p = (d : WithBot ℕ)) (Γ : ℕ → ℝ)
    (hΓ : ∀ j ∈ Finset.Icc 2 d, 0 ≤ Γ j)
    (hhigh : ∀ (m : ℕ) (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2))
      (a : Vec n (ZMod 2)), Function.Injective B → ∀ j, 3 ≤ j → j ≤ d →
      anfDegree (p ∘ affineMap B a) = (j : WithBot ℕ) →
      (vanishingCodim (topForm (p ∘ affineMap B a) j) : ℝ) ≤ Γ j)
    (hquad : ∀ (m : ℕ) (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2))
      (a : Vec n (ZMod 2)), Function.Injective B →
      anfDegree (p ∘ affineMap B a) = (2 : WithBot ℕ) →
      (parityDepth (phase (p ∘ affineMap B a)) : ℝ) ≤ 1 + Γ 2) :
    (parityDepth (phase p) : ℝ) ≤ 1 + ∑ j ∈ Finset.Icc 2 d, Γ j := by sorry

end ParityDegreeDepth.Main
