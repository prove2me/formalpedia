-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_map_dualSub
-- name    : PI.OddDualWeyl.Red.map_dualSub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:57.925794+00:00
-- url     : https://prove2.me/theorems/26dbb0cc-e29b-4d50-bea4-7ace93643e95
-- title:
--   Red: map dual Sub
-- statement:
--   The Red construction uses the map dual Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L165-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L165-L176

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

theorem PI.OddDualWeyl.Red.map_dualSub {S : Type*} [CommRing S] (ψ : R →+* S) (q : MvPolynomial (Fin k × Fin k) R) :
    map ψ (dualSub R k q) = dualSub S k (map ψ q) := by sorry
