-- Prove2me | Theorems.Thm_PI_OddDualWeyl_weyl_rowDiv
-- name    : PI.OddDualWeyl.weyl_rowDiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:30.081048+00:00
-- url     : https://prove2.me/theorems/5a0f9eef-f3c7-4abe-aafe-bfbcd263df58
-- title:
--   Odd Dual Weyl: weyl row Div
-- statement:
--   The Odd Dual Weyl construction uses the weyl row Div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L47-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L47-L55

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

theorem PI.OddDualWeyl.weyl_rowDiv {ν : Fin k → ℕ} (a b : Fin k) (j : ℕ) {f : MvPolynomial (Fin k × Fin k) R}
    (hf : f ∈ weyl R k k le_rfl ν) : rowDiv R a b j f ∈ weyl R k k le_rfl ν := by sorry
