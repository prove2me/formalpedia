-- Prove2me | Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_apply_in_out_b74a29dc527c
-- name    : P2M_PI_QnLevBasicsW__Lev_apply_in_out_b74a29dc527c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:29:06.927898+00:00
-- url     : https://prove2.me/theorems/1a2c6a28-bd34-4004-a428-09c1b388ff6c
-- title:
--   P2 M PI Qn Lev Basics W  Lev apply in out b74a29dc527c: P2 M PI Qn Lev Basics W  Lev apply in out b74a29dc527c
-- statement:
--   The P2 M PI Qn Lev Basics W  Lev apply in out b74a29dc527c construction uses the P2 M PI Qn Lev Basics W  Lev apply in out b74a29dc527c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/LevelGroupUnitaryHermitian.lean#L30-L34

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

theorem P2M_PI_QnLevBasicsW__Lev_apply_in_out_b74a29dc527c (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (p q : Fin (2 * (i + r') + k + 1)) (hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)
    (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) : ιLev k i r' g p q = 0 := by sorry

alias «PI».«QnLevBasicsW».«ιLev_apply_in_out» := P2M_PI_QnLevBasicsW__Lev_apply_in_out_b74a29dc527c
