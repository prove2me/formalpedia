-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_mulLC_apply
-- name    : PositivityTheory.RgUd.T2.HaarDistr.mulLC_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:14.820975+00:00
-- url     : https://prove2.me/theorems/d202fffb-7340-40ee-80f5-fc518cbd048f
-- title:
--   Haar Distr: mul LC apply
-- statement:
--   The Haar Distr construction uses the mul LC apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/FrobeniusReciprocity/HaarDistr.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/FrobeniusReciprocity/HaarDistr.lean#L52-L54

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_PowNear
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob GroundTheory.Automorphic
open scoped Pointwise
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T2 PositivityTheory.RgUd.T2.HaarDistr
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

theorem PositivityTheory.RgUd.T2.HaarDistr.mulLC_apply (ψ : G → ℂ) (hψ : IsLocallyConstant ψ) (α : SB G) (x : G) :
    ((mulLC ψ hψ α : SB G) : G → ℂ) x = ψ x * (α : G → ℂ) x := by sorry

attribute [defeq] PositivityTheory.RgUd.T2.HaarDistr.mulLC_apply
