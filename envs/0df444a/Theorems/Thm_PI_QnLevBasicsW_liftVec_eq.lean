-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_liftVec_eq
-- name    : PI.QnLevBasicsW.liftVec_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:08:19.752171+00:00
-- url     : https://prove2.me/theorems/71b67168-7103-4434-859a-033f060d82e4
-- title:
--   Qn Lev Basics W: lift Vec eq
-- statement:
--   The Qn Lev Basics W construction uses the lift Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L102-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L102-L118

import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
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
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}

theorem PI.QnLevBasicsW.liftVec_eq (v : Fin (2 * r' + k + 1) → ℂ) :
    liftVec k i r' v = (Sum.elim v 0) ∘ (split k i r') := by sorry
