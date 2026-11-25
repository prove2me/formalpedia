-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Specmeas_ofR_smul
-- name    : PositivityTheory.Rg.BcB.E2.P.Specmeas.ofR_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:46.153676+00:00
-- url     : https://prove2.me/theorems/4dcc0e81-ca9d-4f0a-ab7f-c81b18e8f2a8
-- title:
--   Specmeas: of R smul
-- statement:
--   The Specmeas construction uses the of R smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/EigenvalueSeparation/AlmostEverywhereEigen/PositiveMeasureNorms/Specmeas.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/EigenvalueSeparation/AlmostEverywhereEigen/PositiveMeasureNorms/Specmeas.lean#L22-L23

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Specmeas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ComplexConjugate ComplexOrder CompactlySupported
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P PositivityTheory.Rg.BcB.E2.P.Specmeas
variable {X : Type} [TopologicalSpace X]

theorem PositivityTheory.Rg.BcB.E2.P.Specmeas.ofR_smul (c : ℝ) (g : C(X, ℝ)) : ofR (c • g) = (c : ℂ) • ofR g := by sorry
