-- Prove2me | Theorems.Thm_PI_PhMeasCore_UnitaryGroupMassFormula_contDiff_mulRight
-- name    : PI.PhMeasCore.UnitaryGroupMassFormula.contDiff_mulRight
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:35.838431+00:00
-- url     : https://prove2.me/theorems/9a62d24b-4e90-50e7-8780-f06362450ef1
-- title:
--   Unitary Group Mass Formula: cont Diff mul Right
-- statement:
--   The Unitary Group Mass Formula construction uses the cont Diff mul Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/ContDiffMulRight.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/ContDiffMulRight.lean#L43-L45

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_ContDiffMulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open PI PI.PhMeasCore PI.PhMeasCore.UnitaryGroupMassFormula
open PI.PhMeasCore
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem PI.PhMeasCore.UnitaryGroupMassFormula.contDiff_mulRight {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x * g) := by sorry
