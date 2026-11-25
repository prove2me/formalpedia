-- Prove2me | Theorems.Thm_PI_SqfPrimeFactor_W_monicDeg_fn_monic
-- name    : PI.SqfPrimeFactor.W.monicDeg_fn_monic
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:26:35.797933+00:00
-- url     : https://prove2.me/theorems/433fea5d-b485-554e-9ae9-3d3b6efd0894
-- title:
--   W: monic Deg fn monic
-- statement:
--   The W construction uses the monic Deg fn monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/MonicDegFnNatDegree.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/MonicDegFnNatDegree.lean#L11-L13

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

theorem PI.SqfPrimeFactor.W.monicDeg_fn_monic (d : ℕ) (c : Fin d → ZMod g) :
    (X ^ d + ∑ i, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).Monic := by sorry
