-- Prove2me | Theorems.Thm_SNumbers_L1Linf_trunc_coord_of_le
-- name    : SNumbers.L1Linf.trunc_coord_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:54:14.5678+00:00
-- url     : https://prove2.me/theorems/fa5d8954-dfa5-422b-817b-c42c26355e6f
-- title:
--   L1 Linf: trunc coord of le
-- statement:
--   From the truncation index on, the coordinates of `Aₘ` vanish.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L561-L563
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L561-L563

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

theorem SNumbers.L1Linf.trunc_coord_of_le (m : ℕ) (x : L2 𝕜) {j : ℕ} (hj : m ≤ j) :
    (trunc A m x) j = 0 := by sorry
