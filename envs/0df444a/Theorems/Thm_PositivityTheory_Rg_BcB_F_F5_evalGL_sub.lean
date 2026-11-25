-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_F_F5_evalGL_sub
-- name    : PositivityTheory.Rg.BcB.F.F5.evalGL_sub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:52:35.10654+00:00
-- url     : https://prove2.me/theorems/01d505ab-0e31-595e-8b91-4a561f729aa2
-- title:
--   F5: eval GL sub
-- statement:
--   The F5 construction uses the eval GL sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/ShuffleChoices/EvalGLShift.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/ShuffleChoices/EvalGLShift.lean#L16-L21

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

theorem PositivityTheory.Rg.BcB.F.F5.evalGL_sub {n : ℕ} (c d : (Fin n → ℤ) →₀ ℂ) (p q : ℂ) (ξ : Fin n → ℂˣ) :
    evalGL (p • c - q • d) ξ = p * evalGL c ξ - q * evalGL d ξ := by sorry
