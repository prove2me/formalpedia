-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_dot_lift
-- name    : PI.QnLevBasicsW.dot_lift
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:24:43.356521+00:00
-- url     : https://prove2.me/theorems/87efcb09-2f11-4f7b-96bd-f735f13b7bd9
-- title:
--   Qn Lev Basics W: dot lift
-- statement:
--   The Qn Lev Basics W construction uses the dot lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L137-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L137-L142

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

theorem PI.QnLevBasicsW.dot_lift (v w : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k i r' w) ⬝ᵥ liftVec k i r' v = star w ⬝ᵥ v := by sorry
