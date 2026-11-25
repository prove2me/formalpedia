-- Prove2me | Theorems.Thm_SNumbers_L1Linf_emb1_coord
-- name    : SNumbers.L1Linf.emb1_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:53:17.884514+00:00
-- url     : https://prove2.me/theorems/b9928a0e-e8de-46d6-820e-1703fb20c22b
-- title:
--   L1 Linf: emb1 coord
-- statement:
--   Coordinate of `emb1 v` at `j < m`: the `j`-th entry is `vⱼ`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L289-L294
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L289-L294

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

theorem SNumbers.L1Linf.emb1_coord (m : ℕ) (v : EuclideanSpace 𝕜 (Fin m)) (j : Fin m) :
    (emb1 m v) (j : ℕ) = v j := by sorry
