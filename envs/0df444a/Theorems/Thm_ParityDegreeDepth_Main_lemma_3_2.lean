-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_lemma_3_2
-- name    : ParityDegreeDepth.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:46.702247+00:00
-- url     : https://prove2.me/theorems/916cc0e7-2dfe-4c40-a251-89a6a3767d9f
-- title:
--   Lemma 3.2 — binary contraction rank
-- statement:
--   Let $p:\mathbb F_2^n\to\mathbb F_2$ have exact degree $d\ge2$, let $f=(-1)^p$, and put $T=\Delta^d p$. Define $M(T)$ as the maximum binary rank of a two-slot contraction over all $d-2$ binary anchors. Then
--   $$M(T)\le2^{d-1}\log_2\|\widehat f\|_1.$$
--
--   This connects the actual contraction ranks to the Fourier spectral norm. At $d=2$ the anchor tuple is empty.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Lemma 3.2, PDF page 7 / printed page 6.

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

private def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

private def coefficient {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
  then 1 else 0

private def anfDegree {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) : WithBot ℕ :=
  Finset.univ.sup fun S : Finset (Fin n) =>
    if coefficient p S = 0 then ⊥ else (S.card : WithBot ℕ)

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

private def binaryRank {n d : ℕ} (T : Form (ZMod 2) n d) : ℕ :=
  Finset.univ.sup fun h : Fin (d - 2) → Vec n (ZMod 2) => (contraction T h).rank


/-- lemma 3 2; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem lemma_3_2 {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hd : 2 ≤ d) (hp : anfDegree p = (d : WithBot ℕ)) :
    (binaryRank (topForm p d) : ℝ) ≤ (2 : ℝ) ^ (d - 1) * logTwo (spectralNorm (phase p)) := by sorry

end ParityDegreeDepth.Main
