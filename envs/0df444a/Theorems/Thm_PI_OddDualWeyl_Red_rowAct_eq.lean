-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_rowAct_eq
-- name    : PI.OddDualWeyl.Red.rowAct_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:01.370965+00:00
-- url     : https://prove2.me/theorems/8740361b-60c5-49b1-8ab0-790c2f6d625c
-- title:
--   Red: row Act eq
-- statement:
--   The Red construction uses the row Act eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L82-L85

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

theorem PI.OddDualWeyl.Red.rowAct_eq (g : Matrix (Fin k) (Fin k) R) : rowAct R g = sbs (cM g * genM R k) := by sorry
