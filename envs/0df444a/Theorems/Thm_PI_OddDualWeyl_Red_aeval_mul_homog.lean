-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Red_aeval_mul_homog
-- name    : PI.OddDualWeyl.Red.aeval_mul_homog
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:10.760944+00:00
-- url     : https://prove2.me/theorems/f0afb247-e3b9-4641-9d90-4ec4b6afb092
-- title:
--   Red: aeval mul homog
-- statement:
--   The Red construction uses the aeval mul homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L107-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/AevalMulHomog.lean#L107-L120

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

theorem PI.OddDualWeyl.Red.aeval_mul_homog {σ S : Type*} [CommRing S] [Algebra R S] (b : σ → S) (c : S)
    {p : MvPolynomial σ R} {D : ℕ} (hp : p.IsHomogeneous D) :
    aeval (fun v => c * b v) p = c ^ D * aeval b p := by sorry
