-- Prove2me | Theorems.Thm_PI_OddDualWeyl_EvA_arith
-- name    : PI.OddDualWeyl.EvA.arith
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:01.071159+00:00
-- url     : https://prove2.me/theorems/613ce5a8-de94-47d0-94d3-6d61ed8c720c
-- title:
--   Ev A: arith
-- statement:
--   The Ev A construction uses the arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/EvalDuality.lean#L36-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/EvalDuality.lean#L36-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_EvalDuality
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
open PI PI.OddDualWeyl PI.OddDualWeyl.EvA
open Red
variable {K : Type} [Field K]

theorem PI.OddDualWeyl.EvA.arith (x s : K) (hx : x ≠ 0) (hs : s * s = 1) (e e' : ℤ) (D M : ℕ)
    (h : e + e' + (D : ℤ) = (M : ℤ)) (y : K) :
    x ^ e * y = (x⁻¹ * s) ^ e' * (s ^ e' * (x⁻¹ ^ D * (x ^ M * y))) := by sorry
