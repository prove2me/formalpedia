-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_F_F5_evalGL_shift
-- name    : PositivityTheory.Rg.BcB.F.F5.evalGL_shift
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:52:28.167665+00:00
-- url     : https://prove2.me/theorems/1fd0d35c-cab4-538a-a376-d5a2ba168826
-- title:
--   F5: eval GL shift
-- statement:
--   The F5 construction uses the eval GL shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/ShuffleChoices/EvalGLShift.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/ShuffleChoices/EvalGLShift.lean#L8-L14

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_FiniteDiscreteFamilies_PeakCone
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_ShuffleChoices_EvalGLShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.F5

theorem PositivityTheory.Rg.BcB.F.F5.evalGL_shift {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ) (y : Fin n → ℤ) (ξ : Fin n → ℂˣ) :
    evalGL (c.mapDomain (· + y)) ξ = ((∏ i, ξ i ^ y i : ℂˣ) : ℂ) * evalGL c ξ := by sorry
