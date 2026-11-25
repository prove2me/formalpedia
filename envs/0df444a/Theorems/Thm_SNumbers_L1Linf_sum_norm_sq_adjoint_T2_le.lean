-- Prove2me | Theorems.Thm_SNumbers_L1Linf_sum_norm_sq_adjoint_T2_le
-- name    : SNumbers.L1Linf.sum_norm_sq_adjoint_T2_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:15:16.658657+00:00
-- url     : https://prove2.me/theorems/2f733d07-91d0-4e06-94fc-62c31eb30217
-- title:
--   L1 Linf: sum norm sq adjoint T2 le
-- statement:
--   Hilbert–Schmidt bound for the adjoint of the right factor along an
--   orthonormal-or-zero family: `∑ₖ ‖T₂* vₖ‖² ≤ ‖B‖²`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L494-L498
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L494-L498

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

theorem SNumbers.L1Linf.sum_norm_sq_adjoint_T2_le {v : ℕ → L2 𝕜} (hv : SVD.OrthonormalOrZero 𝕜 v)
    (s : Finset ℕ) :
    ∑ k ∈ s, ‖ContinuousLinearMap.adjoint (T2 B) (v k)‖ ^ 2 ≤ ‖B‖ ^ 2 := by sorry
