-- Prove2me | Theorems.Thm_RiskBargaining_proposition_1
-- name    : RiskBargaining.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:28:51.227107+00:00
-- url     : https://prove2.me/theorems/e09bbd5f-ac8b-4d75-84f5-8f01a900da80
-- title:
--   Proposition 1 (corrected: $\mathcal U$ is compact iff the max in (8) exists)
-- statement:
--   Let $(R,M,\mathcal A)$ be a feasible instance. Then
--   $$
--   \mathcal U(R,M,\mathcal A)\text{ is compact}\iff\text{the maximum in (8) exists}.
--   $$
--
--   The paper claims compactness on every instance under Assumption 1. This holds only on attained instances, and the equivalence records the exact condition. No bound $\mathcal A\le\mathbb E$ is assumed.
--
--   Differences from the source:
--   - correction: under Assumption 1 the set 𝒰(R,M,𝒜) is compact → for feasible instances, 𝒰 is compact if and only if the max in (8) exists; reason: the printed claim fails; see RiskBargaining.proposition_1_counterexample (Ω = {1,2,3} uniform, 𝒜_±, ρ = 1/20, M = (11, 11, 8), R_1 = R_2 = 1), and the proof's bound 𝒜_i ≤ E does not follow from Definition 1
--   - generalization: p ≥ 1, values v_i > 0 (p.8) → p = ∞ admitted, positivity of v not assumed; reason: neither is used by the statement; the paper's case is a special case
--   - encoding: M : 𝒳 × Ω → ℝ → M : X → Lp ℝ p μ; reason: Assumption 1 makes x ↦ M_x a map into L^p
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Proposition 1, p.9

import Mathlib
import Definitions.Def_RiskBargaining_Instance_U
import Definitions.Def_RiskBargaining_Instance_Feasible
import Definitions.Def_RiskBargaining_Instance_Attained

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

/-- **Proposition 1, corrected: `𝒰` is compact exactly when the max in (8) exists.**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Proposition 1, p.9.

For a feasible instance, `𝒰(R, M, 𝒜)` is compact in `ℝⁿ` if and only if (8) attains its maximum.

**Formalization Note.** The printed claim is that `𝒰` is compact under Assumption 1, without condition.
That fails (`RiskBargaining.proposition_1_counterexample`). No bound `𝒜 ≤ E` is assumed. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (X : Type*) [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι] [Nonempty ι] (I : Instance μ p X ι) (hI : I.Feasible) :
    IsCompact I.U ↔ I.Attained := by sorry

end RiskBargaining
