-- Prove2me | Theorems.Thm_PI_SqfRootsInj_W_divCount
-- name    : PI.SqfRootsInj.W.divCount
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:32.173823+00:00
-- url     : https://prove2.me/theorems/77e02d18-b9fc-4d7b-8e98-e7e3daaefd23
-- title:
--   W: div Count
-- statement:
--   The W construction uses the div Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/DivCount.lean#L11-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/DivCount.lean#L11-L48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_ClaimOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_DivCount
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
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W

theorem PI.SqfRootsInj.W.divCount {g : ℕ} [Fact g.Prime] (r : ℕ) (T : Finset (ZMod g)[X])
    (hT : ∀ f ∈ T, f.Monic ∧ f.natDegree = r) (h : (ZMod g)[X]) (hh : h.Monic) :
    (T.filter (h ∣ ·)).card ≤ g ^ (r - h.natDegree) := by sorry
