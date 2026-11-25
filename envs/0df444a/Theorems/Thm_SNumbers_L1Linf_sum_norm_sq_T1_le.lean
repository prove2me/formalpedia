-- Prove2me | Theorems.Thm_SNumbers_L1Linf_sum_norm_sq_T1_le
-- name    : SNumbers.L1Linf.sum_norm_sq_T1_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:15:03.23808+00:00
-- url     : https://prove2.me/theorems/4cd2bab4-b7d7-46ca-859c-0110464e3b3b
-- title:
--   L1 Linf: sum norm sq T1 le
-- statement:
--   Hilbert–Schmidt bound for the left factor along an orthonormal-or-zero
--   family: `∑ₖ ‖T₁ uₖ‖² ≤ ‖A‖²`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L487-L490
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L487-L490

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

theorem SNumbers.L1Linf.sum_norm_sq_T1_le {u : ℕ → L2 𝕜} (hu : SVD.OrthonormalOrZero 𝕜 u) (s : Finset ℕ) :
    ∑ k ∈ s, ‖T1 A (u k)‖ ^ 2 ≤ ‖A‖ ^ 2 := by sorry
