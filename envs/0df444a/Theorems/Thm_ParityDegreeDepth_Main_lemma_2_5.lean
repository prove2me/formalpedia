-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_lemma_2_5
-- name    : ParityDegreeDepth.Main.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:01.7812+00:00
-- url     : https://prove2.me/theorems/2cba39bd-8060-4dd4-8054-7394cc255834
-- title:
--   Lemma 2.5 — multiplicative derivative norm
-- statement:
--   For any Boolean phase $f=(-1)^p$ on $\mathbb F_2^n$, any $k\ge0$, and any directions $h_1,\ldots,h_k$, put $D_hf(x)=f(x)f(x+h)$. Then
--   $$\|\widehat{D_{h_1}\cdots D_{h_k}f}\|_1\le\|\widehat f\|_1^{2^k}.$$
--
--   This bounds the spectral cost of repeated multiplicative differentiation, including the empty sequence of directions.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Lemma 2.5, PDF page 5 / printed page 4.

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

private def signDerivatives {n k : ℕ} (f : Vec n (ZMod 2) → ℝ)
    (h : Fin k → Vec n (ZMod 2)) : Vec n (ZMod 2) → ℝ :=
  (List.ofFn h).foldl (fun g v x => g x * g (x + v)) f


/-- lemma 2 5; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem lemma_2_5 {n k : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (h : Fin k → Vec n (ZMod 2)) :
    spectralNorm (signDerivatives (phase p) h) ≤ spectralNorm (phase p) ^ (2 ^ k) := by sorry

end ParityDegreeDepth.Main
