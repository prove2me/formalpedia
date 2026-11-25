-- Prove2me | Theorems.Thm_PI_PhMeasCore_UnitaryGroupMassFormula_mul_mem_UH
-- name    : PI.PhMeasCore.UnitaryGroupMassFormula.mul_mem_UH
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:42.547947+00:00
-- url     : https://prove2.me/theorems/d52794ac-ca0d-4b3a-8b71-5b356e83bf1e
-- title:
--   Unitary Group Mass Formula: mul mem UH
-- statement:
--   The Unitary Group Mass Formula construction uses the mul mem UH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/ContDiffMulRight.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/ContDiffMulRight.lean#L12-L19

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

theorem PI.PhMeasCore.UnitaryGroupMassFormula.mul_mem_UH {n : ℕ} {Hm a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UH Hm) (hb : b ∈ UH Hm) :
    a * b ∈ UH Hm := by sorry
