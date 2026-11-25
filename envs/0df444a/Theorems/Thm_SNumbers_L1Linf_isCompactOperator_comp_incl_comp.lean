-- Prove2me | Theorems.Thm_SNumbers_L1Linf_isCompactOperator_comp_incl_comp
-- name    : SNumbers.L1Linf.isCompactOperator_comp_incl_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:15:16.103941+00:00
-- url     : https://prove2.me/theorems/b6ce6f00-da86-556e-b035-0ee3dff71d9c
-- title:
--   L1 Linf: is Compact Operator comp incl comp
-- statement:
--   If `A` has finite rank, so has `B I A`, and it is therefore compact.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L513-L515
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L513-L515

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

theorem SNumbers.L1Linf.isCompactOperator_comp_incl_comp {m : ℕ} (hrank : A.rank ≤ (m : Cardinal)) :
    IsCompactOperator (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)) := by sorry
