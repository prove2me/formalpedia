-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_intLC_ind_ne_zero
-- name    : PositivityTheory.RgUd.T2.HaarDistr.intLC_ind_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:56.589328+00:00
-- url     : https://prove2.me/theorems/41baa71e-87d0-5bba-a917-ad1bbda5188f
-- title:
--   Haar Distr: int LC ind ne zero
-- statement:
--   The Haar Distr construction uses the int LC ind ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/FrobeniusReciprocity/HaarDistr.lean#L136-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/FrobeniusReciprocity/HaarDistr.lean#L136-L144

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
variable [MeasurableSpace G] [BorelSpace G]

theorem PositivityTheory.RgUd.T2.HaarDistr.intLC_ind_ne_zero (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) : intLC μ (ind K hK) ≠ 0 := by sorry
