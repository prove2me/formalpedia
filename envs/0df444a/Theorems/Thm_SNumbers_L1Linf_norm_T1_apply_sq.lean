-- Prove2me | Theorems.Thm_SNumbers_L1Linf_norm_T1_apply_sq
-- name    : SNumbers.L1Linf.norm_T1_apply_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:14:59.966261+00:00
-- url     : https://prove2.me/theorems/331a3970-4a32-417a-aee8-71c52f41a671
-- title:
--   L1 Linf: norm T1 apply sq
-- statement:
--   `‖T₁ x‖² = ∑ⱼ |⟪rowⱼ, x⟫|²`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L462-L465
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L462-L465

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

theorem SNumbers.L1Linf.norm_T1_apply_sq (x : L2 𝕜) :
    ‖T1 A x‖ ^ 2 = ∑' j, ‖(inner 𝕜 (row A j) x : 𝕜)‖ ^ 2 := by sorry
