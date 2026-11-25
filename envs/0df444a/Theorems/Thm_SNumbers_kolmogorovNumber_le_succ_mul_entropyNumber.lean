-- Prove2me | Theorems.Thm_SNumbers_kolmogorovNumber_le_succ_mul_entropyNumber
-- name    : SNumbers.kolmogorovNumber_le_succ_mul_entropyNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:11:18.32637+00:00
-- url     : https://prove2.me/theorems/0feb9f44-33df-44c3-878b-657f71a2174c
-- title:
--   SNumbers: kolmogorov Number le succ mul entropy Number
-- statement:
--   **The entropy bound for the Kolmogorov numbers**: `dₙ(S) ≤ (n+1) · eₙ(S)`
--   (Pietsch, *Operator ideals*, 12.3.2).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L574-L667
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L574-L667

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

theorem SNumbers.kolmogorovNumber_le_succ_mul_entropyNumber (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n ≤ ((n : ℝ) + 1) * entropyNumber S n := by sorry
