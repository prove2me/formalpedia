-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_map_det_genM
-- name    : PI.OddDualWeyl.Red.map_det_genM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:23.084904+00:00
-- url     : https://prove2.me/theorems/5c692a24-e274-41b8-96ed-96e629b7a236
-- title:
--   Red: map det gen M
-- statement:
--   The Red construction uses the map det gen M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L178-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L178-L182

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

theorem PI.OddDualWeyl.Red.map_det_genM {S : Type*} [CommRing S] (ψ : R →+* S) :
    map ψ (genM R k).det = (genM S k).det := by sorry
