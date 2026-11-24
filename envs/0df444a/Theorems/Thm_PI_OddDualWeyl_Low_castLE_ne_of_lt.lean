-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Low_castLE_ne_of_lt
-- name    : PI.OddDualWeyl.Low.castLE_ne_of_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:47.167747+00:00
-- url     : https://prove2.me/theorems/df302b93-7c37-4678-83a0-fbd590309340
-- title:
--   Low: cast LE ne of lt
-- statement:
--   The Low construction uses the cast LE ne of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L131-L133

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
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
open PI PI.OddDualWeyl PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]
variable {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)

theorem PI.OddDualWeyl.Low.castLE_ne_of_lt {s : ℕ} (h : s ≤ n + 1) (p : Fin s) (j : Fin (n + 1)) (hj : p.val < j.val) :
    Fin.castLE h p ≠ j := by sorry
