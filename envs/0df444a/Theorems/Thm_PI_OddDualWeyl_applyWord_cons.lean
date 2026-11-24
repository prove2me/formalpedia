-- Prove2me | Theorems.Thm_PI_OddDualWeyl_applyWord_cons
-- name    : PI.OddDualWeyl.applyWord_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:21.466096+00:00
-- url     : https://prove2.me/theorems/436da057-bc28-4b1f-9c89-baded5c4a17e
-- title:
--   Odd Dual Weyl: apply Word cons
-- statement:
--   The Odd Dual Weyl construction uses the apply Word cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L59-L60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose
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
variable {R : Type} [CommRing R] {k M : ℕ}

theorem PI.OddDualWeyl.applyWord_cons (x : Fin k × Fin k × ℕ) (w : List (Fin k × Fin k × ℕ)) (f : MvPolynomial (Fin k × Fin k) R) :
    applyWord R (x :: w) f = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f) := by sorry
