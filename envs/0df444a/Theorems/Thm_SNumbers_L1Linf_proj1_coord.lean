-- Prove2me | Theorems.Thm_SNumbers_L1Linf_proj1_coord
-- name    : SNumbers.L1Linf.proj1_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:14:29.2158+00:00
-- url     : https://prove2.me/theorems/a6e65edd-3e29-4aae-950b-82d504b79b16
-- title:
--   L1 Linf: proj1 coord
-- statement:
--   Coordinate of `proj1 y`: the `j`-th entry is `y j`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L354-L356
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L354-L356

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

theorem SNumbers.L1Linf.proj1_coord (m : ℕ) (y : L1 𝕜) (j : Fin m) :
    (proj1 m : L1 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y j = y (j : ℕ) := by sorry
