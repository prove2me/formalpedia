-- Prove2me | Theorems.Thm_RiskBargaining_split_admissible_z
-- name    : RiskBargaining.split_admissible_z
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:30:43.985847+00:00
-- url     : https://prove2.me/theorems/ec8d72e6-6627-462e-b373-06a4952d7f92
-- title:
--   Appendix A.3, p.37 (corrected: on the admissible class) — splitting a player preserves the class and $z$
-- statement:
--   Let $(R,M,\mathcal A)$ be admissible, $i$ a player and $\ell\ge 1$, and let $(R',M,\mathcal A')$ be the game associated with splitting $i$ into $\ell$ players. Then $(R',M,\mathcal A')$ is admissible, $z(R',M,\mathcal A')=z(R,M,\mathcal A)$, and
--   $$
--   v'_j=v_j\ \ (j\ne i),\qquad v'_{ik}=\frac{v_i}{\ell}\ \ (k=1,\dots,\ell).
--   $$
--   This shows that the admissible class is closed under the operation of Axiom 3, and that the axiom compares games with the same total.
--
--   Differences from the source:
--   - correction: the claim z = z′ is made for every feasible instance, with z the max in (8) → stated on admissible instances, where the max in (8) exists; reason: the max can fail to exist on a feasible instance; see RiskBargaining.proposition_1_counterexample (Ω = {1,2,3} uniform, 𝒜_±, ρ = 1/20, M = (11, 11, 8), R_1 = R_2 = 1)
--   - generalization: z = z′ and the formulas for v′ → also: the split instance is admissible; reason: the page uses this silently, because F must be defined there
--   - generalization: p ≥ 1 → p : ℝ≥0∞ with 1 ≤ p, so p = ∞ is admitted; reason: the page does not say whether p = ∞ is meant; finite p is a special case
--   - encoding: M : 𝒳 × Ω → ℝ; N′ = N∖{i} ∪ {(i,k) | k = 1,…,ℓ} → M : X → Lp ℝ p μ; player type {j // j ≠ i} ⊕ Fin ℓ with ℓ : ℕ+; reason: the same instances and the same game
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Appendix A.3, proof of Theorem 1, p.37

import Mathlib
import Definitions.Def_RiskBargaining_Instance_z
import Definitions.Def_RiskBargaining_Instance_Admissible
import Definitions.Def_RiskBargaining_Instance_split

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

/-- **Splitting a player preserves the class and `z`, and divides the value.**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Appendix A.3, proof of Theorem 1, p.37: "it is easy to see that z = z′ for the corresponding
solution values of (8). Then, v′j = vj (j ≠ i), v′ik = vi/ℓ (k = 1,...,ℓ)".

If `I` is admissible and `ℓ ≥ 1`, the split of `I` at `i` into `ℓ` players is admissible, has the same `z`,
and has `v′_j = v_j` for `j ≠ i` and `v′_ik = v_i / ℓ`. -/
theorem split_admissible_z {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (X : Type*) [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (I : Instance μ p X ι) (hI : I.Admissible)
    (i : ι) (ℓ : ℕ+) :
    (I.split i ℓ).Admissible ∧ (I.split i ℓ).z = I.z ∧
      (∀ j : {j // j ≠ i}, (I.split i ℓ).v (Sum.inl j) = I.v j) ∧
      (∀ k : Fin ℓ, (I.split i ℓ).v (Sum.inr k) = I.v i / ((ℓ : ℕ) : ℝ)) := by sorry

end RiskBargaining
