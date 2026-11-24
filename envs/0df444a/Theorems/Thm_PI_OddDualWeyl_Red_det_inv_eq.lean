-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_det_inv_eq
-- name    : PI.OddDualWeyl.Red.det_inv_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:01.087748+00:00
-- url     : https://prove2.me/theorems/134c4fe7-c67f-4908-91c4-e690dbc8c5a7
-- title:
--   Red: det inv eq
-- statement:
--   The Red construction uses the det inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L188-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L188-L192

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
variable {K : Type*} [Field K] {k : ℕ}

theorem PI.OddDualWeyl.Red.det_inv_eq (g : Matrix (Fin k) (Fin k) K) : (g⁻¹).det = (g.det)⁻¹ := by sorry
