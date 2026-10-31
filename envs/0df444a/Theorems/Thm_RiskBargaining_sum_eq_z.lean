-- Prove2me | Theorems.Thm_RiskBargaining_sum_eq_z
-- name    : RiskBargaining.sum_eq_z
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:31:08.790015+00:00
-- url     : https://prove2.me/theorems/987f1751-16e0-47fe-ad73-9246907367c2
-- title:
--   Appendix A.3, p.36 (corrected: on the admissible class) — PAR forces $\sum_i u^*_i=z$
-- statement:
--   Let $F$ be a bargaining solution satisfying PAR and let $(R,M,\mathcal A)$ be admissible. Then, for $u^*=F(R,M,\mathcal A)$,
--   $$
--   \sum_{i=1}^n u^*_i=z(R,M,\mathcal A).
--   $$
--   This places every Pareto optimal solution on the upper face of the polytope (7).
--
--   Differences from the source:
--   - correction: the sum is computed for every feasible instance, with z the max in (8) → stated on admissible instances, where the max in (8) exists; reason: the max can fail to exist on a feasible instance; see RiskBargaining.proposition_1_counterexample (Ω = {1,2,3} uniform, 𝒜_±, ρ = 1/20, M = (11, 11, 8), R_1 = R_2 = 1)
--   - generalization: F satisfies Axioms 1 – 3; p ≥ 1 → F satisfies PAR alone; p = ∞ admitted; reason: the page uses only PAR at this step; the paper's case is a special case
--   - reading: X, Y and p are not listed in an instance; a bargaining solution acts on instances → X, Y, p are fixed parameters; F is a family over all finite nonempty player types; reason: Definition 2 lists only (R, M, 𝒜), and Axiom 3 changes the player set
--   - encoding: M : 𝒳 × Ω → ℝ → M : X → Lp ℝ p μ; reason: Assumption 1 makes x ↦ M_x a map into L^p
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Appendix A.3, proof of Theorem 1, p.36

import Mathlib
import Definitions.Def_RiskBargaining_IsBargainingSolution
import Definitions.Def_RiskBargaining_PAR
import Definitions.Def_RiskBargaining_Instance_z

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

/-- **PAR forces the sum `z`.**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Appendix A.3, proof of Theorem 1, p.36.

For a bargaining solution with PAR and an admissible instance, `∑ i, F i = z`. -/
theorem sum_eq_z {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (X : Type*) [TopologicalSpace X] [CompactSpace X]
    (F : Rule μ p X) (hF : IsBargainingSolution F) (hPAR : PAR F)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (I : Instance μ p X ι)
    (hI : I.Admissible) :
    ∑ i, F ι I i = I.z := by sorry

end RiskBargaining
