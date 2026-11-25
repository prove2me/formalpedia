-- Prove2me | Theorems.Thm_SNumbers_L1Linf_projinf_coord
-- name    : SNumbers.L1Linf.projinf_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:42:33.734901+00:00
-- url     : https://prove2.me/theorems/c02252ba-aff8-5f5e-8b9d-64e76ec00a42
-- title:
--   L1 Linf: projinf coord
-- statement:
--   Coordinate of `proj∞ y`: the `j`-th entry is `y j`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L260-L264
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L260-L264

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

theorem SNumbers.L1Linf.projinf_coord (m : ℕ) (y : Linf 𝕜) (j : Fin m) :
    (projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y j = y (j : ℕ) := by sorry
