-- Prove2me | Theorems.Thm_SNumbers_L1Linf_projinf_apply
-- name    : SNumbers.L1Linf.projinf_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:13:13.448911+00:00
-- url     : https://prove2.me/theorems/f6a3b912-da6d-5a99-9809-b51bc72eb596
-- title:
--   L1 Linf: projinf apply
-- statement:
--   The L1 Linf construction uses the projinf apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L253-L257
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L253-L257

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

theorem SNumbers.L1Linf.projinf_apply (m : ℕ) (y : Linf 𝕜) :
    (projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y
      = ∑ i : Fin m, (y (i : ℕ)) • EuclideanSpace.single i (1 : 𝕜) := by sorry
