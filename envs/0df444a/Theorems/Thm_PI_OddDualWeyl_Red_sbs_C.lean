-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_sbs_C
-- name    : PI.OddDualWeyl.Red.sbs_C
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:19.430805+00:00
-- url     : https://prove2.me/theorems/eb57af88-a7e0-4301-889a-42c02c541213
-- title:
--   Red: sbs C
-- statement:
--   The Red construction uses the sbs C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L25-L29

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

theorem PI.OddDualWeyl.Red.sbs_C (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) (r : R) :
    sbs A (C r) = C r := by sorry
