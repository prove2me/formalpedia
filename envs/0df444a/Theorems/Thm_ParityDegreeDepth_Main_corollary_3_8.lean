-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_corollary_3_8
-- name    : ParityDegreeDepth.Main.corollary_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:01.475529+00:00
-- url     : https://prove2.me/theorems/cb63fc3e-ab91-4eaf-84b7-6056a5c97858
-- title:
--   Corollary 3.8 — vanishing subspace codimension
-- statement:
--   Let $p:\mathbb F_2^n\to\mathbb F_2$ have exact degree $d\ge3$, set $f=(-1)^p$ and $T=\Delta^d p$, and let $R$ be its generic two-slot contraction rank. Then
--   $$c(T)\le R\le2^{2d-3}\log_2\|\widehat f\|_1.$$
--
--   Here $c(T)$ is the actual minimum vanishing codimension, so the first comparison gives a binary subspace of controlled codimension.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Corollary 3.8, PDF page 12 / printed page 11.

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

private def Vanishes {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (U : Submodule F (Vec n F)) : Prop := ∀ x, (∀ i, x i ∈ U) → T x = 0

private def vanishingCodim {n d : ℕ} (T : Form (ZMod 2) n d) : ℕ :=
  sInf {r | ∃ U : Submodule (ZMod 2) (Vec n (ZMod 2)),
    n - Module.finrank (ZMod 2) U = r ∧ Vanishes T U}

private abbrev AnchorRing (F : Type) [CommRing F] (n k : ℕ) := MvPolynomial (Fin k × Fin n) F

private abbrev AnchorField (F : Type) [Field F] (n k : ℕ) := FractionRing (AnchorRing F n k)

private def genericMatrix {F : Type} [Field F] {n d : ℕ} (T : Form F n d) :
    Matrix (Fin n) (Fin n) (AnchorRing F n (d - 2)) :=
  fun i j => ∑ a : Fin (d - 2) → Fin n,
    MvPolynomial.C (T (fun s => if hs : s.val < d - 2 then Pi.single (a ⟨s.val, hs⟩) 1
      else if s.val = d - 2 then Pi.single i 1 else Pi.single j 1)) *
    ∏ t, MvPolynomial.X (t, a t)

private def genericContraction {F : Type} [Field F] {n d : ℕ} (T : Form F n d) :
    Matrix (Fin n) (Fin n) (AnchorField F n (d - 2)) :=
  (genericMatrix T).map (algebraMap (AnchorRing F n (d - 2)) (AnchorField F n (d - 2)))

private def genericRank {F : Type} [Field F] {n d : ℕ} (T : Form F n d) : ℕ :=
  (genericContraction T).rank


/-- corollary 3 8; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem corollary_3_8 {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hd : 3 ≤ d) (hp : anfDegree p = (d : WithBot ℕ)) :
    vanishingCodim (topForm p d) ≤ genericRank (topForm p d) ∧
    (genericRank (topForm p d) : ℝ) ≤
      (2 : ℝ) ^ (2 * d - 3) * logTwo (spectralNorm (phase p)) := by sorry

end ParityDegreeDepth.Main
