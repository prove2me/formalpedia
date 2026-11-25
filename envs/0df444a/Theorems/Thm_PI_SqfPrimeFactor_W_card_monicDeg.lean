-- Prove2me | Theorems.Thm_PI_SqfPrimeFactor_W_card_monicDeg
-- name    : PI.SqfPrimeFactor.W.card_monicDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:11.579172+00:00
-- url     : https://prove2.me/theorems/c4346fee-3827-4580-892a-8e2dc6889343
-- title:
--   W: card monic Deg
-- statement:
--   The W construction uses the card monic Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/MonicDegFnNatDegree.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/MonicDegFnNatDegree.lean#L47-L54

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

theorem PI.SqfPrimeFactor.W.card_monicDeg (d : ℕ) : (monicDeg g d).card = g ^ d := by sorry
