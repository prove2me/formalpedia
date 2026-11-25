-- Prove2me | Theorems.Thm_SNumbers_L1Linf_sum_norm_sq_row_le_norm_sq
-- name    : SNumbers.L1Linf.sum_norm_sq_row_le_norm_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:14:48.705796+00:00
-- url     : https://prove2.me/theorems/a9487079-b402-49c1-b917-b93d7c2689f4
-- title:
--   L1 Linf: sum norm sq row le norm sq
-- statement:
--   Hilbert–Schmidt bound for the left factor, via its rows:
--   `∑ⱼ ‖rowⱼ‖² ≤ ‖A‖²`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L450-L451
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L450-L451

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_AddOns_Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_SNumbers_Examples_IdentityL1Linfty
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)

theorem SNumbers.L1Linf.sum_norm_sq_row_le_norm_sq (J : Finset ℕ) : ∑ j ∈ J, ‖row A j‖ ^ 2 ≤ ‖A‖ ^ 2 := by sorry
