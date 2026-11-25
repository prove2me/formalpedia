-- Prove2me | Theorems.Thm_PI_SqfPrimeFactor_W_mem_irrDeg
-- name    : PI.SqfPrimeFactor.W.mem_irrDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:19.379416+00:00
-- url     : https://prove2.me/theorems/a7625b3c-debb-4381-8ec4-e3ae89de1ba3
-- title:
--   W: mem irr Deg
-- statement:
--   The W construction uses the mem irr Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/MonicDegFnNatDegree.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/MonicDegFnNatDegree.lean#L57-L60

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
open Classical

theorem PI.SqfPrimeFactor.W.mem_irrDeg {d : ℕ} {q : (ZMod g)[X]} :
    q ∈ irrDeg g d ↔ (q.Monic ∧ q.natDegree = d) ∧ Irreducible q := by sorry
