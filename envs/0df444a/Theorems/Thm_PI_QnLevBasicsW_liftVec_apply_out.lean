-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_liftVec_apply_out
-- name    : PI.QnLevBasicsW.liftVec_apply_out
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:28:10.587408+00:00
-- url     : https://prove2.me/theorems/d5ae3c5d-1f8a-4e21-b08e-e5986692764c
-- title:
--   Qn Lev Basics W: lift Vec apply out
-- statement:
--   The Qn Lev Basics W construction uses the lift Vec apply out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L47-L50

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
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

theorem PI.QnLevBasicsW.liftVec_apply_out (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) : liftVec k i r' v p = 0 := by sorry
