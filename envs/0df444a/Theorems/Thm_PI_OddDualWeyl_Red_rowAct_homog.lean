-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_rowAct_homog
-- name    : PI.OddDualWeyl.Red.rowAct_homog
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:13:57.237874+00:00
-- url     : https://prove2.me/theorems/5de6ad4d-bfa6-4b3b-bd3d-ef8a2a3548c2
-- title:
--   Red: row Act homog
-- statement:
--   The Red construction uses the row Act homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L122-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L122-L151

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

theorem PI.OddDualWeyl.Red.rowAct_homog (g : Matrix (Fin k) (Fin k) R) {p : MvPolynomial (Fin k × Fin k) R} {D : ℕ}
    (hp : p.IsHomogeneous D) : (rowAct R g p).IsHomogeneous D := by sorry
