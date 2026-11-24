-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_map_mul_sbs
-- name    : PI.OddDualWeyl.Red.map_mul_sbs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:19.329473+00:00
-- url     : https://prove2.me/theorems/6a3543a7-ff3c-46f3-a020-279cd173eb4a
-- title:
--   Red: map mul sbs
-- statement:
--   The Red construction uses the map mul sbs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L65-L68

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

theorem PI.OddDualWeyl.Red.map_mul_sbs (A M N : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) :
    (M * N).map (sbs A) = M.map (sbs A) * N.map (sbs A) := by sorry
