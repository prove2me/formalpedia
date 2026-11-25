-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_n_sub_S
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.SW.n_sub_S
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:38:02.211456+00:00
-- url     : https://prove2.me/theorems/54ee9739-08af-48d2-a373-287b91afb448
-- title:
--   SW: n sub S
-- statement:
--   The SW construction uses the n sub S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MulVecBvecApply.lean#L242-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MulVecBvecApply.lean#L242-L245

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem PI.QuotSetU.UnitaryGroupMassFormula.SW.n_sub_S {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r) :
    n ∈ Sset k r z := by sorry
