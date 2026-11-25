-- Prove2me | Theorems.Thm_SNumbers_L1Linf_sum_norm_sq_col_le_norm_sq
-- name    : SNumbers.L1Linf.sum_norm_sq_col_le_norm_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:14:23.93411+00:00
-- url     : https://prove2.me/theorems/18fef0fe-91ee-4e7a-9da6-14c12d79de20
-- title:
--   L1 Linf: sum norm sq col le norm sq
-- statement:
--   Hilbert–Schmidt bound for the right factor, via its columns:
--   `∑ⱼ ‖colⱼ‖² ≤ ‖B‖²`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L458-L459
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L458-L459

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

theorem SNumbers.L1Linf.sum_norm_sq_col_le_norm_sq (J : Finset ℕ) : ∑ j ∈ J, ‖col B j‖ ^ 2 ≤ ‖B‖ ^ 2 := by sorry
