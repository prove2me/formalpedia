-- Prove2me | Theorems.Thm_SNumbers_L1Linf_comp_incl_comp_eq
-- name    : SNumbers.L1Linf.comp_incl_comp_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:15:16.712684+00:00
-- url     : https://prove2.me/theorems/29e68b80-fd8a-5060-bece-083bb97c1b8a
-- title:
--   L1 Linf: comp incl comp eq
-- statement:
--   `B I A` factors through `ℓ₂` as the product of the two Hilbert–Schmidt
--   factors `T₂ = B J₂` and `T₁ = J₁ A`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L519-L521
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L519-L521

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

theorem SNumbers.L1Linf.comp_incl_comp_eq : B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A) = (T2 B).comp (T1 A) := by sorry
