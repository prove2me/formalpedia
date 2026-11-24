-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_herm_lift
-- name    : PI.QnLevBasicsW.herm_lift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:08:00.664993+00:00
-- url     : https://prove2.me/theorems/c4d2f737-25ac-4533-91e2-31a18b739aab
-- title:
--   Qn Lev Basics W: herm lift
-- statement:
--   The Qn Lev Basics W construction uses the herm lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L179-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L179-L182

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

theorem PI.QnLevBasicsW.herm_lift (v w : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (i + r')) (liftVec k i r' v) (liftVec k i r' w) = herm (Hpk k r') v w := by sorry
