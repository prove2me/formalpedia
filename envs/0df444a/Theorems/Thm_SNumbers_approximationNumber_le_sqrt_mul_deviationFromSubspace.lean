-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_le_sqrt_mul_deviationFromSubspace
-- name    : SNumbers.approximationNumber_le_sqrt_mul_deviationFromSubspace
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:55:13.209132+00:00
-- url     : https://prove2.me/theorems/d7f09aca-5189-4d8e-8ed9-e2631d53272b
-- title:
--   SNumbers: approximation Number le sqrt mul deviation From Subspace
-- statement:
--   **Kolmogorov half, per subspace.** For `V ⊆ Y` of dimension `≤ n`,
--   `aₙ(S) ≤ (1 + √n)·‖π_V ∘ S‖`. The approximant is `L := P ∘ S` for the
--   Kadets–Snobar projection `P` onto `V`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L498-L538
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L498-L538

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X] [CompleteSpace Y]
omit [CompleteSpace X] [CompleteSpace Y]

theorem SNumbers.approximationNumber_le_sqrt_mul_deviationFromSubspace
    (S : X →L[𝕜] Y) {n : ℕ} {V : Submodule 𝕜 Y}
    (hV_rank : Module.rank 𝕜 V ≤ (n : Cardinal)) :
    approximationNumber S n ≤ (1 + Real.sqrt n) * deviationFromSubspace S V := by sorry
