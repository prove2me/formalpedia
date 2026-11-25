-- Prove2me | Theorems.Thm_SNumbers_L1Linf_norm_adjoint_T2_apply_sq
-- name    : SNumbers.L1Linf.norm_adjoint_T2_apply_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:14:42.405663+00:00
-- url     : https://prove2.me/theorems/c319c2c7-dfd3-4dfe-914b-5eb8cccb0c35
-- title:
--   L1 Linf: norm adjoint T2 apply sq
-- statement:
--   `‖T₂* y‖² = ∑ⱼ |⟪colⱼ, y⟫|²`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L475-L478
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L475-L478

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

theorem SNumbers.L1Linf.norm_adjoint_T2_apply_sq (y : L2 𝕜) :
    ‖ContinuousLinearMap.adjoint (T2 B) y‖ ^ 2 = ∑' j, ‖(inner 𝕜 (col B j) y : 𝕜)‖ ^ 2 := by sorry
