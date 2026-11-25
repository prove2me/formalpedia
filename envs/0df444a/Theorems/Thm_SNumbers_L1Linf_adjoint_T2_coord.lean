-- Prove2me | Theorems.Thm_SNumbers_L1Linf_adjoint_T2_coord
-- name    : SNumbers.L1Linf.adjoint_T2_coord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:16:22.87798+00:00
-- url     : https://prove2.me/theorems/076fd9dd-1ab2-4195-bd2f-027929c27a0b
-- title:
--   L1 Linf: adjoint T2 coord
-- statement:
--   Coordinates of the adjoint of the right factor: `(T₂* y)ⱼ = ⟪colⱼ, y⟫`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L468-L472
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L468-L472

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

theorem SNumbers.L1Linf.adjoint_T2_coord (y : L2 𝕜) (j : ℕ) :
    (ContinuousLinearMap.adjoint (T2 B) y) j = (inner 𝕜 (col B j) y : 𝕜) := by sorry
