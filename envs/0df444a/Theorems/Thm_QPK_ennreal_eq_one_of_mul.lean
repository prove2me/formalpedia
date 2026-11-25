-- Prove2me | Theorems.Thm_QPK_ennreal_eq_one_of_mul
-- name    : QPK.ennreal_eq_one_of_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:08.143712+00:00
-- url     : https://prove2.me/theorems/1a4cc204-a65b-4e53-a132-e04bdb3d1d60
-- title:
--   QPK: ennreal eq one of mul
-- statement:
--   The QPK construction uses the ennreal eq one of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/ConjugationInvariantMeasure.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/ConjugationInvariantMeasure.lean#L10-L13

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_ConjugationInvariantMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open scoped ENNReal
open QPK

theorem QPK.ennreal_eq_one_of_mul {a b : ℝ≥0∞} (h0 : b ≠ 0) (ht : b ≠ ⊤) (h : a * b = b) : a = 1 := by sorry
