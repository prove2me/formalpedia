-- Prove2me | Theorems.Thm_SNumbers_kolmogorovNumber_two_pow_le_entropyNumber
-- name    : SNumbers.kolmogorovNumber_two_pow_le_entropyNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:22:13.470502+00:00
-- url     : https://prove2.me/theorems/9af2a08f-5afb-473a-af17-0707b1dfd67a
-- title:
--   SNumbers: kolmogorov Number two pow le entropy Number
-- statement:
--   **`d_{2ⁿ} S ≤ eₙ S`.** A cover of `S(B_X)` by `2 ^ n` balls of radius `ε`
--   gives a subspace of dimension at most `2 ^ n`, the span of the centres, from
--   which `S(B_X)` deviates by at most `ε`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L206-L211
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L206-L211

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.kolmogorovNumber_two_pow_le_entropyNumber (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S (2 ^ n) ≤ entropyNumber S n := by sorry
