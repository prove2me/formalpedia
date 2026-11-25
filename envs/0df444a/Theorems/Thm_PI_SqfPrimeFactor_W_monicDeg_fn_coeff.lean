-- Prove2me | Theorems.Thm_PI_SqfPrimeFactor_W_monicDeg_fn_coeff
-- name    : PI.SqfPrimeFactor.W.monicDeg_fn_coeff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:26:25.344684+00:00
-- url     : https://prove2.me/theorems/3a96d85b-f692-4f58-b9a1-6442e2aaa489
-- title:
--   W: monic Deg fn coeff
-- statement:
--   The W construction uses the monic Deg fn coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/MonicDegFnNatDegree.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/MonicDegFnNatDegree.lean#L21-L31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_BigPrimes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
variable {g : ℕ} [Fact g.Prime]

theorem PI.SqfPrimeFactor.W.monicDeg_fn_coeff (d : ℕ) (c : Fin d → ZMod g) (i : Fin d) :
    (X ^ d + ∑ j, C (c j) * X ^ (j : ℕ) : (ZMod g)[X]).coeff i = c i := by sorry
