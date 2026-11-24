-- Prove2me | Theorems.Thm_QPK_haar_measure_uniqueness
-- name    : QPK.haar_measure_uniqueness
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:55:27.363793+00:00
-- url     : https://prove2.me/theorems/174a0c51-cf27-4fba-8928-88ebc8552e29
-- title:
--   QPK: haar measure uniqueness
-- statement:
--   The QPK construction uses the haar measure uniqueness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/HaarMeasureUniqueness.lean#L62-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/HaarMeasureUniqueness.lean#L62-L111

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

theorem QPK.haar_measure_uniqueness : HaarUniq := by sorry
