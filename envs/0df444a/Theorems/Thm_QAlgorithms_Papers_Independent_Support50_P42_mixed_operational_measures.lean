-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_mixed_operational_measures
-- name    : QAlgorithms.Papers.Independent.Support50.P42.mixed_operational_measures
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:26:16.556738+00:00
-- url     : https://prove2.me/theorems/56eb2a55-0df8-454c-ac8e-5b10a09756be
-- title:
--   Operational formation and distillation measures
-- statement:
--   For a normalized density $\rho$ on positive finite local dimensions, let $E_C(\rho)$ be the infimum of nonnegative eventual singlet-consumption rates for preparing $\rho^{\otimes n}$ by local protocols with vanishing global error. Let $E_D(\rho)$ be the supremum of eventual singlet-production rates from $\rho^{\otimes n}$ with the same global accuracy convention. Formation rates form a nonempty set bounded below, zero distillation is feasible, and distillation rates are bounded above. For pure inputs and local output ensembles,
--
--   $$E_C(\psi)=E_D(\psi)=S(\rho_B),\qquad \sum_jp_jE_C(\rho_j)\le E_C(\rho),\quad \sum_jp_jE_D(\rho_j)\le E_D(\rho).$$
--
--   The expectation inequalities hold for finite adaptive local protocols, including mixed output branches. This uses the paper's operational formation measure, not the later single-copy convex roof; no mixed-state reversibility is claimed.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 17, §V: operational formation and distillation measures

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.17: operational formation and distillation reduce to pure-state
entropy and cannot increase in expectation under local protocols. Feasibility
and boundedness guards are conclusions, never optimizer hypotheses. -/
theorem mixed_operational_measures :
    (∀ s : Shared, {R | FormationRate s R}.Nonempty ∧ BddBelow {R | FormationRate s R} ∧
      SingletDistillationRate s 0 ∧ BddAbove {R | SingletDistillationRate s R} ∧
      (IsPureShared s → formationCost s=ent s ∧ singletDistillable s=ent s)) ∧
    (∀ (s : Shared) (out : List (ℝ × Shared)), LocalTree s out →
      (out.map fun w => w.1*formationCost w.2).sum ≤ formationCost s ∧
      (out.map fun w => w.1*singletDistillable w.2).sum ≤ singletDistillable s) := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
