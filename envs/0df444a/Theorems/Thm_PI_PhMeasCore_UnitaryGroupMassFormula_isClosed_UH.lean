-- Prove2me | Theorems.Thm_PI_PhMeasCore_UnitaryGroupMassFormula_isClosed_UH
-- name    : PI.PhMeasCore.UnitaryGroupMassFormula.isClosed_UH
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:47.563424+00:00
-- url     : https://prove2.me/theorems/711d47f1-3e22-47f2-a9c8-2f144a8492f9
-- title:
--   Unitary Group Mass Formula: is Closed UH
-- statement:
--   The Unitary Group Mass Formula construction uses the is Closed UH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/Development.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/Development.lean#L55-L56

import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.PhMeasCore PI.PhMeasCore.UnitaryGroupMassFormula
open PI.PhMeasCore

theorem PI.PhMeasCore.UnitaryGroupMassFormula.isClosed_UH {n : ℕ} (Hm : Matrix (Fin n) (Fin n) ℂ) : IsClosed (UH Hm) := by sorry
