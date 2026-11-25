-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_isLocallyConstant_char
-- name    : PositivityTheory.RgUd.T2.HaarDistr.isLocallyConstant_char
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:06.323114+00:00
-- url     : https://prove2.me/theorems/fa09b9f2-b07a-49fd-9118-945f6c87bb2c
-- title:
--   Haar Distr: is Locally Constant char
-- statement:
--   The Haar Distr construction uses the is Locally Constant char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/FrobeniusReciprocity/HaarDistr.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/FrobeniusReciprocity/HaarDistr.lean#L30-L37

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

theorem PositivityTheory.RgUd.T2.HaarDistr.isLocallyConstant_char (χ : G →* ℂˣ) (hχ : Continuous (fun g => (χ g : ℂ))) :
    IsLocallyConstant (fun g => (χ g : ℂ)) := by sorry
