-- Prove2me | Theorems.Thm_PI_QnLevBasicsW_liftVec_apply_in
-- name    : PI.QnLevBasicsW.liftVec_apply_in
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:27:57.827991+00:00
-- url     : https://prove2.me/theorems/26e8f498-a3b8-4f64-ac30-0465c25b87be
-- title:
--   Qn Lev Basics W: lift Vec apply in
-- statement:
--   The Qn Lev Basics W construction uses the lift Vec apply in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L36-L45

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

theorem PI.QnLevBasicsW.liftVec_apply_in (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (i + r') + k + 1))
    (a : Fin (2 * r' + k + 1)) (hp : p.val = a.val + i) : liftVec k i r' v p = v a := by sorry
