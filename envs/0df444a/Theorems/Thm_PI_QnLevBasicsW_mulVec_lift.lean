-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_mulVec_lift
-- name    : PI.QnLevBasicsW.mulVec_lift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:08:03.304961+00:00
-- url     : https://prove2.me/theorems/4eba4b56-fa8f-44ca-b707-7316fa5e4997
-- title:
--   Qn Lev Basics W: mul Vec lift
-- statement:
--   The Qn Lev Basics W construction uses the mul Vec lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L131-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean#L131-L135

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

theorem PI.QnLevBasicsW.mulVec_lift (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (v : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k i r' g *ᵥ liftVec k i r' v = liftVec k i r' (g *ᵥ v) := by sorry
