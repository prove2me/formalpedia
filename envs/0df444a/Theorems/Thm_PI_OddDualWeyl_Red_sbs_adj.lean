-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_sbs_adj
-- name    : PI.OddDualWeyl.Red.sbs_adj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:13:58.255829+00:00
-- url     : https://prove2.me/theorems/aea6b31d-6cd5-4fa5-aef9-1663ddb52c8d
-- title:
--   Red: sbs adj
-- statement:
--   The Red construction uses the sbs adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L77-L80

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

theorem PI.OddDualWeyl.Red.sbs_adj (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) (i j : Fin k) :
    sbs A ((genM R k).adjugate i j) = A.adjugate i j := by sorry
