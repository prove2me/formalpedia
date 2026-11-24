-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_sbs_X
-- name    : PI.OddDualWeyl.Red.sbs_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:34.068495+00:00
-- url     : https://prove2.me/theorems/ab69a73c-7f92-4cc0-8b22-8282b4078915
-- title:
--   Red: sbs X
-- statement:
--   The Red construction uses the sbs X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L19-L23

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

theorem PI.OddDualWeyl.Red.sbs_X (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) (v : Fin k × Fin k) :
    sbs A (X v) = A v.1 v.2 := by sorry
