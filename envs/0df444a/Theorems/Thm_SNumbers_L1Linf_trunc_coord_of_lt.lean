-- Prove2me | Theorems.Thm_SNumbers_L1Linf_trunc_coord_of_lt
-- name    : SNumbers.L1Linf.trunc_coord_of_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:53:40.881867+00:00
-- url     : https://prove2.me/theorems/ce171380-f766-558b-97cd-6dca97c985b4
-- title:
--   L1 Linf: trunc coord of lt
-- statement:
--   Below the truncation index the coordinates of `Aₘ` agree with those of `A`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L554-L558
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L554-L558

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

theorem SNumbers.L1Linf.trunc_coord_of_lt (m : ℕ) (x : L2 𝕜) {j : ℕ} (hj : j < m) :
    (trunc A m x) j = A x j := by sorry
