-- Prove2me | Theorems.Thm_PI_TOW_filter_concatW_length
-- name    : PI.TOW.filter_concatW_length
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:37:49.88486+00:00
-- url     : https://prove2.me/theorems/d63c6468-c0fc-4b52-a1b5-1b71c20da34e
-- title:
--   TOW: filter concat W length
-- statement:
--   The TOW construction uses the filter concat W length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FilterConcatWLength.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FilterConcatWLength.lean#L21-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FilterConcatWLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW
open PI.TO

theorem PI.TOW.filter_concatW_length {n' k : ℕ} (w : Fin n' → List (Fin k × Fin k)) (t : Fin n') :
    ((concatW w).filter fun z => z.1 = t).length = (w t).length := by sorry
