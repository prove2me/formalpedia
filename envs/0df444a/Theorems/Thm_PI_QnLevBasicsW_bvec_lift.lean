-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_bvec_lift
-- name    : PI.QnLevBasicsW.bvec_lift
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:24:49.58543+00:00
-- url     : https://prove2.me/theorems/19c636e2-a9a3-4e0f-a301-30f916ce0639
-- title:
--   Qn Lev Basics W: bvec lift
-- statement:
--   The Qn Lev Basics W construction uses the bvec lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L52-L62

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

theorem PI.QnLevBasicsW.bvec_lift (a : Fin (2 * r' + k + 1)) (q : Fin (2 * (i + r') + k + 1)) (hq : q.val = a.val + i) :
    liftVec k i r' (bvec a) = bvec q := by sorry
