-- Prove2me | Theorems.Thm_PI_SqPairLocal_intAt_inv_mul
-- name    : PI.SqPairLocal.intAt_inv_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:23:59.053244+00:00
-- url     : https://prove2.me/theorems/f6f684c2-cea4-423e-883a-aedcf1ade873
-- title:
--   Sq Pair Local: int At inv mul
-- statement:
--   The Sq Pair Local construction uses the int At inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/DivAtOneOfInt.lean#L88-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/DivAtOneOfInt.lean#L88-L95

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime]

theorem PI.SqPairLocal.intAt_inv_mul {c : 𝓞 E} (hc : (c : E) ≠ 0) {x : E} (hx : DivAt Q c x) :
    IntAt Q ((c : E)⁻¹ * x) := by sorry
