-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_rowAct_one
-- name    : PI.OddDualWeyl.Red.rowAct_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:11.258823+00:00
-- url     : https://prove2.me/theorems/ffb0e489-a9ed-4776-b7b6-4e9e984f4e6c
-- title:
--   Red: row Act one
-- statement:
--   The Red construction uses the row Act one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L92-L93

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

theorem PI.OddDualWeyl.Red.rowAct_one (p : MvPolynomial (Fin k × Fin k) R) : rowAct R (1 : Matrix (Fin k) (Fin k) R) p = p := by sorry
