-- Prove2me | Theorems.Thm_SNumbers_entropyNumber_zero_eq_norm
-- name    : SNumbers.entropyNumber_zero_eq_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:04:12.892191+00:00
-- url     : https://prove2.me/theorems/fc6d9c4c-18e7-589c-8e0d-f6b222127a46
-- title:
--   SNumbers: entropy Number zero eq norm
-- statement:
--   **`e₀(S) = ‖S‖`**: one ball suffices for radius `‖S‖`, and no smaller radius does.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L303-L306
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L303-L306

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

theorem SNumbers.entropyNumber_zero_eq_norm (S : X →L[𝕜] Y) : entropyNumber S 0 = ‖S‖ := by sorry
