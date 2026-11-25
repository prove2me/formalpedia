-- Prove2me | Theorems.Thm_SNumbers_max_gelfandNumber_kolmogorovNumber_le_succ_mul_entropyNumber
-- name    : SNumbers.max_gelfandNumber_kolmogorovNumber_le_succ_mul_entropyNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:23:02.795137+00:00
-- url     : https://prove2.me/theorems/3d9a08f3-ae5e-452d-a2c8-8a622f990b35
-- title:
--   SNumbers: max gelfand Number kolmogorov Number le succ mul entropy Number
-- statement:
--   **Pietsch 12.3.2**: `max(cₙ(S), dₙ(S)) ≤ (n+1) · eₙ(S)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L912-L917
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L912-L917

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

theorem SNumbers.max_gelfandNumber_kolmogorovNumber_le_succ_mul_entropyNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n) ≤
      ((n : ℝ) + 1) * entropyNumber S n := by sorry
