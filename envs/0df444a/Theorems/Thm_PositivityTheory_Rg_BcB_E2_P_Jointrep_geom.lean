-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Jointrep_geom
-- name    : PositivityTheory.Rg.BcB.E2.P.Jointrep.geom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:03.310526+00:00
-- url     : https://prove2.me/theorems/a5e10676-aef0-40a8-aacc-e2296250c879
-- title:
--   Jointrep: geom
-- statement:
--   The Jointrep construction uses the geom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/EigenvalueSeparation/AlmostEverywhereEigen/PositiveMeasureNorms/Jointrep.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/EigenvalueSeparation/AlmostEverywhereEigen/PositiveMeasureNorms/Jointrep.lean#L12-L17

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Jointrep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
open PositivityTheory.Rg.BcB.E2.P.Jointrep

theorem PositivityTheory.Rg.BcB.E2.P.Jointrep.geom : (∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹ ^ j) ^ 2) ≠ ⊤ := by sorry
