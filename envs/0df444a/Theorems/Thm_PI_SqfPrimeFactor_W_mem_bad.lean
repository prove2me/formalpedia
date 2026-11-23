-- Prove2me | Theorems.Thm_PI_SqfPrimeFactor_W_mem_bad
-- name    : PI.SqfPrimeFactor.W.mem_bad
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:28.382411+00:00
-- url     : https://prove2.me/theorems/dda75434-c1ab-47a7-9893-91c48d9c35a9
-- title:
--   W: mem bad
-- statement:
--   The W construction uses the mem bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/SquarefreeCountEstimate.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/SquarefreeCountEstimate.lean#L43-L49

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_SquarefreeCountEstimate
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
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]

theorem PI.SqfPrimeFactor.W.mem_bad {r p : ℕ} {f : (ZMod g)[X]} (hf : f ∈ bad g r p) :
    ∃ q h : (ZMod g)[X], f = q * h ∧ q.Monic ∧ q.natDegree = p ∧ Irreducible q ∧
      h.Monic ∧ h.natDegree = r - p := by sorry
