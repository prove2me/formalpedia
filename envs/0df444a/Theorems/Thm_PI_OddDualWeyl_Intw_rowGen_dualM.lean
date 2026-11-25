-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Intw_rowGen_dualM
-- name    : PI.OddDualWeyl.Intw.rowGen_dualM
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:17.643232+00:00
-- url     : https://prove2.me/theorems/028cd479-24cd-45b4-88d0-adb67c295139
-- title:
--   Intw: row Gen dual M
-- statement:
--   The Intw construction uses the row Gen dual M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/TransvectionMulApply.lean#L80-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/TransvectionMulApply.lean#L80-L96

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_TransvectionMulApply
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
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Intw
variable {R : Type} [CommRing R] {k : ℕ}

theorem PI.OddDualWeyl.Intw.rowGen_dualM (a b : Fin k) (hab : a ≠ b) (i j : Fin k) :
    rowGen R a b (dualM R k i j) = Polynomial.C (dualM R k i j) -
      (if i = a then Polynomial.X * Polynomial.C (dualM R k b j) else 0) := by sorry
