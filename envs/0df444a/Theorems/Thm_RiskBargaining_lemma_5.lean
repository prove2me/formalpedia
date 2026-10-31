-- Prove2me | Theorems.Thm_RiskBargaining_lemma_5
-- name    : RiskBargaining.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:30:40.108272+00:00
-- url     : https://prove2.me/theorems/02cd1f83-43fe-41a0-bef5-0cf47a615a93
-- title:
--   Lemma 5 (corrected: on the admissible class; generalized: $z$ does not depend on $R$)
-- statement:
--   Let $(R,M,\mathcal A)$ and $(R',M,\mathcal A)$ be two instances with the same $M$ and $\mathcal A$, with values $v$ and $v'$.
--
--   1. If $(R,M,\mathcal A)$ is admissible, $v'_i>0$ for all $i$, and $\sum_i v'_i\le z(R,M,\mathcal A)$, then $(R',M,\mathcal A)$ is admissible and $z(R',M,\mathcal A)=z(R,M,\mathcal A)$.
--   2. If both instances are admissible, then $z(R',M,\mathcal A)=z(R,M,\mathcal A)$.
--
--   So $z$ is constant in $v$ on the admissible values, which implies the continuity asserted by the paper.
--
--   Differences from the source:
--   - correction: the map v ↦ z is treated for every feasible instance, with z the max in (8) → stated on admissible instances, where the max in (8) exists; reason: the max can fail to exist on a feasible instance; see RiskBargaining.proposition_1_counterexample (Ω = {1,2,3} uniform, 𝒜_±, ρ = 1/20, M = (11, 11, 8), R_1 = R_2 = 1)
--   - generalization: v ↦ z(R,M,𝒜) is continuous → z takes one value on all admissible instances with the same M and 𝒜, and admissibility passes to smaller positive values; reason: a constant function is continuous, so this implies the printed lemma
--   - generalization: p ≥ 1 → p : ℝ≥0∞ with 1 ≤ p, so p = ∞ is admitted; reason: the page does not say whether p = ∞ is meant; finite p is a special case
--   - encoding: M : 𝒳 × Ω → ℝ → M : X → Lp ℝ p μ; reason: Assumption 1 makes x ↦ M_x a map into L^p
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Lemma 5, p.35

import Mathlib
import Definitions.Def_RiskBargaining_Instance_z
import Definitions.Def_RiskBargaining_Instance_Admissible

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

/-- **Lemma 5, generalized: `z` does not depend on the endowments.**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Lemma 5, p.35.

Let `I`, `I'` share `M` and `𝒜` and differ only in the endowments.

1. If `I` is admissible, `v' > 0` and `∑ i, v' i ≤ z(I)`, then `I'` is admissible and `z(I') = z(I)`.
2. If `I` and `I'` are both admissible, then `z(I') = z(I)`.

**Formalization Note.** The printed Lemma 5 is the continuity of `v ↦ z`. A function constant on the
feasible values is continuous there, so this implies it. -/
theorem lemma_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (X : Type*) [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι] [Nonempty ι] (I I' : Instance μ p X ι)
    (hM : I'.M = I.M) (hA : I'.A = I.A) :
    (I.Admissible → (∀ i, 0 < I'.v i) → ∑ i, I'.v i ≤ I.z → I'.Admissible ∧ I'.z = I.z) ∧
      (I.Admissible → I'.Admissible → I'.z = I.z) := by sorry

end RiskBargaining
