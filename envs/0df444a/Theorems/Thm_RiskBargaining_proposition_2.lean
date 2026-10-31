-- Prove2me | Theorems.Thm_RiskBargaining_proposition_2
-- name    : RiskBargaining.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:29:46.411019+00:00
-- url     : https://prove2.me/theorems/b3648d1d-8579-4462-8c3b-fd2b361e6eda
-- title:
--   Proposition 2 (corrected: where the max in (8) exists) — $\mathcal U$ is the polytope (7)
-- statement:
--   Let $(R,M,\mathcal A)$ be an instance for which the maximum in (8) exists, with value $z=z(R,M,\mathcal A)$ and $v_i=\mathcal A_i(R_i)$. Then
--   $$
--   \mathcal U(R,M,\mathcal A)=\Big\{u\in\mathbb R^n \;\Big|\; \forall i\in N: u_i\ge v_i,\ \sum_{i=1}^n u_i\le z\Big\},
--   $$
--   and $z$ is the greatest element of the value set of (8).
--
--   This reduces the bargaining game to a simplex-like set in $\mathbb R^n$, which is the form in which Axioms 1–3 are applied.
--
--   Differences from the source:
--   - correction: the polytope claim, proved by appeal to Proposition 1, for every feasible instance, with z the max in (8) → stated on admissible instances, where the max in (8) exists; reason: the max can fail to exist on a feasible instance; see RiskBargaining.proposition_1_counterexample (Ω = {1,2,3} uniform, 𝒜_±, ρ = 1/20, M = (11, 11, 8), R_1 = R_2 = 1)
--   - generalization: p ≥ 1, values v_i > 0 (p.8) → p = ∞ admitted, positivity of v not assumed; reason: neither is used by the statement; the paper's case is a special case
--   - encoding: M : 𝒳 × Ω → ℝ → M : X → Lp ℝ p μ; reason: Assumption 1 makes x ↦ M_x a map into L^p
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Proposition 2, p.9; proof in Appendix A.2, pp.34–35

import Mathlib
import Definitions.Def_RiskBargaining_Instance_U
import Definitions.Def_RiskBargaining_Instance_z
import Definitions.Def_RiskBargaining_Instance_Attained

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

/-- **Proposition 2, corrected: `𝒰` is the polytope (7).**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Proposition 2, p.9, with proof in Appendix A.2, pp.34–35.

If the max in (8) exists, then `𝒰(R, M, 𝒜) = {u | ∀ i, v i ≤ u i, ∑ i, u i ≤ z}` and `z` is that max.

**Formalization Note.** The hypothesis `Attained` replaces the appeal to Proposition 1, which fails
(`RiskBargaining.proposition_1_counterexample`). Without it the `max` of (8) has no meaning. Positivity of
`v` is not needed. -/
theorem proposition_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (X : Type*) [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι] [Nonempty ι] (I : Instance μ p X ι) (hI : I.Attained) :
    I.U = {u | (∀ i, I.v i ≤ u i) ∧ ∑ i, u i ≤ I.z} ∧ IsGreatest I.totals I.z := by sorry

end RiskBargaining
