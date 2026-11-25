-- Prove2me | Theorems.Thm_PI_TOW_LiftW_inj
-- name    : PI.TOW.LiftW.inj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:28:56.770963+00:00
-- url     : https://prove2.me/theorems/87828c79-e785-5194-bb12-9e874ed0b77b
-- title:
--   Lift W: inj
-- statement:
--   The Lift W construction uses the inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/NotMemVarsEmbS.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/NotMemVarsEmbS.lean#L13-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_NotMemVarsEmbS
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
open PI PI.TOW PI.TOW.LiftW
open PI.TO PI.TOW
variable {K : Type} [CommRing K] {n' k : ℕ}

theorem PI.TOW.LiftW.inj (t : Fin n') : Function.Injective (fun c : Fin k => (t, c)) := by sorry
