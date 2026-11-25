-- Prove2me | Theorems.Thm_SNumbers_L1Linf_norm_e
-- name    : SNumbers.L1Linf.norm_e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:11:59.600851+00:00
-- url     : https://prove2.me/theorems/406fb479-926d-5039-a149-d7839af775cd
-- title:
--   L1 Linf: norm e
-- statement:
--   `‖eᵢ‖₁ = 1`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L99-L100
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L99-L100

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

theorem SNumbers.L1Linf.norm_e (i : ℕ) : ‖(e i : L1 𝕜)‖ = 1 := by sorry
