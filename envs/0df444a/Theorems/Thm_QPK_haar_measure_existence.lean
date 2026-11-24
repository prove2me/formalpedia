-- Prove2me | Theorems.Thm_QPK_haar_measure_existence
-- name    : QPK.haar_measure_existence
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:18.20474+00:00
-- url     : https://prove2.me/theorems/8adc56b4-9499-4b85-af6e-1a55b4e48434
-- title:
--   QPK: haar measure existence
-- statement:
--   The QPK construction uses the haar measure existence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/HaarMeasureUniqueness.lean#L33-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/HaarMeasureUniqueness.lean#L33-L60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal
open QPK

theorem QPK.haar_measure_existence : HaarExist := by sorry
