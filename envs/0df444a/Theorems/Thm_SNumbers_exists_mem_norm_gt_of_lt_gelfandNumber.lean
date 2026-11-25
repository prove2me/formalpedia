-- Prove2me | Theorems.Thm_SNumbers_exists_mem_norm_gt_of_lt_gelfandNumber
-- name    : SNumbers.exists_mem_norm_gt_of_lt_gelfandNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:19:34.231275+00:00
-- url     : https://prove2.me/theorems/07ba79b2-f52c-49ed-a34f-92dbf0804e9d
-- title:
--   SNumbers: exists mem norm gt of lt gelfand Number
-- statement:
--   **Iterative point selection for the Gelfand numbers.** If `c < cₖ(S)` and `M` is a
--   closed subspace of `X` of codimension `≤ k`, then `M` contains a vector `x` with `‖x‖ ≤ 1`
--   and `‖S x‖ > c` (since `cₖ(S) ≤ ‖S|_M‖ = ⨆_{x∈M} ‖S x‖`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L680-L687
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L680-L687

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

theorem SNumbers.exists_mem_norm_gt_of_lt_gelfandNumber (S : X →L[𝕜] Y) {k : ℕ} {M : Submodule 𝕜 X}
    (hM_closed : IsClosed (M : Set X)) (hM_rank : Module.rank 𝕜 (X ⧸ M) ≤ (k : Cardinal))
    {c : ℝ} (hc : c < gelfandNumber S k) :
    ∃ x ∈ M, ‖x‖ ≤ 1 ∧ c < ‖S x‖ := by sorry
