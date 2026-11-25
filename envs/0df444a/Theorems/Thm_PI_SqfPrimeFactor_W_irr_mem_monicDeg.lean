-- Prove2me | Theorems.Thm_PI_SqfPrimeFactor_W_irr_mem_monicDeg
-- name    : PI.SqfPrimeFactor.W.irr_mem_monicDeg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:26:13.853011+00:00
-- url     : https://prove2.me/theorems/0f32f34a-5129-494f-93c7-e86a779dd4c0
-- title:
--   W: irr mem monic Deg
-- statement:
--   The W construction uses the irr mem monic Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/IrreducibleCountLowerBound.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/IrreducibleCountLowerBound.lean#L9-L16

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_BigPrimes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_IrreducibleCountLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W

theorem PI.SqfPrimeFactor.W.irr_mem_monicDeg {g d : ℕ} [Fact g.Prime] {q : (ZMod g)[X]} (hq : q.Monic)
    (hd : q.natDegree = d) : q ∈ monicDeg g d := by sorry
