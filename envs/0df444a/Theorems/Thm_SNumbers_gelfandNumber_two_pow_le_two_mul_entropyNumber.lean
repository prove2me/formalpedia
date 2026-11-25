-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_two_pow_le_two_mul_entropyNumber
-- name    : SNumbers.gelfandNumber_two_pow_le_two_mul_entropyNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:21:54.66281+00:00
-- url     : https://prove2.me/theorems/d5f9cc7d-c235-5336-bb0c-800150e1b256
-- title:
--   SNumbers: gelfand Number two pow le two mul entropy Number
-- statement:
--   **`c_{2ⁿ} S ≤ 2 · eₙ S`.** The Gelfand counterpart of
--   `kolmogorovNumber_two_pow_le_entropyNumber`; the factor `2` comes from the
--   norming-functional argument.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L216-L225
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L216-L225

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

theorem SNumbers.gelfandNumber_two_pow_le_two_mul_entropyNumber (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S (2 ^ n) ≤ 2 * entropyNumber S n := by sorry
