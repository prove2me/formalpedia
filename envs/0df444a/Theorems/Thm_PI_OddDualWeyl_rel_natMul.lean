-- Prove2me | Theorems.Thm_PI_OddDualWeyl_rel_natMul
-- name    : PI.OddDualWeyl.rel_natMul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:16.005638+00:00
-- url     : https://prove2.me/theorems/fdfe69d2-e5aa-4b65-af84-a0422f29e6d1
-- title:
--   Odd Dual Weyl: rel nat Mul
-- statement:
--   The Odd Dual Weyl construction uses the rel nat Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L28-L32

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

theorem PI.OddDualWeyl.rel_natMul {f f' : MvPolynomial (Fin k × Fin k) R} (n : ℕ) (h : Rel R k M f f') :
    Rel R k M ((n : MvPolynomial (Fin k × Fin k) R) * f) ((n : MvPolynomial (Fin k × Fin k) R) * f') := by sorry
