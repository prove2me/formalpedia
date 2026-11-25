-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_rowAct_rowAct
-- name    : PI.OddDualWeyl.Red.rowAct_rowAct
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:13:47.859047+00:00
-- url     : https://prove2.me/theorems/7d6da1c0-23ea-4f3f-a62d-5eeba446eb5f
-- title:
--   Red: row Act row Act
-- statement:
--   The Red construction uses the row Act row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L87-L90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}

theorem PI.OddDualWeyl.Red.rowAct_rowAct (A B : Matrix (Fin k) (Fin k) R) (p : MvPolynomial (Fin k × Fin k) R) :
    rowAct R A (rowAct R B p) = rowAct R (B * A) p := by sorry
