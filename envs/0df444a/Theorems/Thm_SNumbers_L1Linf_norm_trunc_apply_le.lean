-- Prove2me | Theorems.Thm_SNumbers_L1Linf_norm_trunc_apply_le
-- name    : SNumbers.L1Linf.norm_trunc_apply_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:15:40.50981+00:00
-- url     : https://prove2.me/theorems/f319607c-b19a-5b48-bfce-8668a578b806
-- title:
--   L1 Linf: norm trunc apply le
-- statement:
--   Truncating does not increase the norm: `‖Aₘ x‖₁ ≤ ‖A x‖₁`, since the
--   coordinates of `Aₘ x` are those of `A x` or zero.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L573-L586
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L573-L586

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

theorem SNumbers.L1Linf.norm_trunc_apply_le (m : ℕ) (x : L2 𝕜) : ‖trunc A m x‖ ≤ ‖A x‖ := by sorry
