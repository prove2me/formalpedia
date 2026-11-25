-- Prove2me | Theorems.Thm_PI_OddDualWeyl_mem_of_pm
-- name    : PI.OddDualWeyl.mem_of_pm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:14:55.56642+00:00
-- url     : https://prove2.me/theorems/f7f4d275-196a-43a2-bec6-0571908b2082
-- title:
--   Odd Dual Weyl: mem of pm
-- statement:
--   The Odd Dual Weyl construction uses the mem of pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L62-L66

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

theorem PI.OddDualWeyl.mem_of_pm {S : Submodule R (MvPolynomial (Fin k × Fin k) R)} {x : MvPolynomial (Fin k × Fin k) R}
    (u : MvPolynomial (Fin k × Fin k) R) (hu : u = 1 ∨ u = -1) (hx : x ∈ S) : u * x ∈ S := by sorry
