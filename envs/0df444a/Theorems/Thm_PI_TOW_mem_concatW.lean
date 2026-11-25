-- Prove2me | Theorems.Thm_PI_TOW_mem_concatW
-- name    : PI.TOW.mem_concatW
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:37:36.369815+00:00
-- url     : https://prove2.me/theorems/9a4cea16-ffc3-492e-89f4-00194d983d81
-- title:
--   TOW: mem concat W
-- statement:
--   The TOW construction uses the mem concat W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FilterConcatWLength.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FilterConcatWLength.lean#L12-L19

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

theorem PI.TOW.mem_concatW {n' k : ℕ} (w : Fin n' → List (Fin k × Fin k)) (z : Fin n' × (Fin k × Fin k)) :
    z ∈ concatW w ↔ z.2 ∈ w z.1 := by sorry
