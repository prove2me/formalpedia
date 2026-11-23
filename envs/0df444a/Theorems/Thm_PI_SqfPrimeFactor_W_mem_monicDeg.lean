-- Prove2me | Theorems.Thm_PI_SqfPrimeFactor_W_mem_monicDeg
-- name    : PI.SqfPrimeFactor.W.mem_monicDeg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:58:23.569653+00:00
-- url     : https://prove2.me/theorems/b11cf18f-ff59-4fa3-9d89-7203e254e4f6
-- title:
--   W: mem monic Deg
-- statement:
--   The W construction uses the mem monic Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/MonicDegFnNatDegree.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/MonicDegFnNatDegree.lean#L33-L45

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

theorem PI.SqfPrimeFactor.W.mem_monicDeg {d : ℕ} {f : (ZMod g)[X]} :
    f ∈ monicDeg g d ↔ f.Monic ∧ f.natDegree = d := by sorry
