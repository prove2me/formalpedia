-- Prove2me | Theorems.Thm_SteurerHDX_theorem_3_1
-- name    : SteurerHDX.theorem_3_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:34:02.985015+00:00
-- url     : https://prove2.me/theorems/9e57a166-ec3f-4908-a1b3-1cd4132e7eef
-- title:
--   Theorem 3.1: a down-up gap $\alpha/d$ yields nonnegative unit vectors with average correlation $\le\Delta/n$ and no $2/(\beta\sqrt{\alpha d})$-separated $\beta n$-sets
-- statement:
--   This is the paper's main technical theorem.
--
--   Let $\mathcal X$ be a pure $d$-dimensional complex with $n=|\mathcal X(d)|\ge2$ facets and degree $\Delta$, and let $\alpha>0$. Suppose the spectral gap of the down-up walk satisfies $1-\lambda_2(P_d^\vee)\ge\alpha/d$. Then there are vectors $v_\sigma\in\mathbb R^{\mathcal X(1)}_{\ge0}$, one per facet $\sigma\in\mathcal X(d)$, such that
--
--   1. each $v_\sigma$ is a unit vector with nonnegative coordinates;
--   2. they satisfy the squared triangle inequality $\|v_i-v_j\|^2\le\|v_i-v_k\|^2+\|v_k-v_j\|^2$ for all $i,j,k$;
--   3. (i) $$\mathbb E_{i,j}|\langle v_i,v_j\rangle|=\frac1{n^2}\sum_{i,j}|\langle v_i,v_j\rangle|\le\frac{\Delta}{n};$$
--   4. (ii) for every $0<\beta<1$ and all disjoint sets $A,B$ of facets with $|A|,|B|\ge\beta n$ there are $v_i\in A$, $v_j\in B$ with
--   $$\|v_i-v_j\|_2^2\le\frac{2}{\beta\sqrt{\alpha\cdot d}} .$$
--
--   Applied to the sparse expanders of Theorem 2.4 it produces the vectors of Theorem 1.5.
--
--   **Formalization Note** The vectors live in `EuclideanSpace ℝ (faces X 1)`. Both clauses hold for the same vectors.
--
--   Differences from the source:
--   - encoding: α unrestricted → α > 0; reason: √(α·d) is printed, so α > 0 is implicit; for α ≤ 0 the bound is undefined (Lean would read 2/0 = 0)
--   - encoding: no condition on the number of facets → 2 ≤ |X(d)|; reason: the spectral gap of a one-state chain is undefined; the condition only excludes that case (and forces d ≥ 1)
--   - encoding: v₁, …, v_n ∈ ℝ^{X(1)}_{≥0}, E_{i,j} → a family indexed by the facets in EuclideanSpace ℝ (faces X 1) with nonnegative coordinates; E_{i,j} as (1/n²) Σ_{i,j} over ordered pairs; reason: Lean convention; same instances
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Theorem 3.1, p.5

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_SteurerHDX_degree
import Definitions.Def_SteurerHDX_spectralGap
import Definitions.Def_SteurerHDX_downUp

namespace SteurerHDX

/-- **Theorem 3.1 (main technical theorem).** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Theorem 3.1, p.5: "Let X be a pure
d-dimensional complex with degree ∆, and suppose the spectral gap of the d-dimensional down-up
walk is at least α/d. Then there are n := |X(d)| nonnegative unit vectors v₁, …, v_n ∈ ℝ^{X(1)}_{≥0}
satisfying squared triangle inequality (1.1) such that: (i) E_{i,j}|⟨vᵢ, vⱼ⟩| ≤ ∆/n; (ii) for every
0 < β < 1 and every two disjoint sets of vectors A, B with |A|, |B| ≥ βn, there exist vᵢ ∈ A and
vⱼ ∈ B such that ‖vᵢ − vⱼ‖₂² ≤ 2/(β√(α·d))."

**Formalization Note.** The vectors are indexed by the facets X(d) and live in
`EuclideanSpace ℝ (faces X 1)` = ℝ^{X(1)}; E_{i,j} is the uniform average over ordered pairs
(diagonal included). α > 0 (√(α·d) and α/d are printed) and |X(d)| ≥ 2 (the spectral gap of a
one-state chain is undefined; this also forces d ≥ 1) are assumed. Both clauses hold for the
same vectors. -/
theorem theorem_3_1 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ) (α : ℝ)
    (hX : IsPure X d) (hcard : 2 ≤ (faces X d).card) (hα : 0 < α)
    (hgap : α / d ≤ spectralGap (downUp X d)) :
    ∃ v : faces X d → EuclideanSpace ℝ (faces X 1),
      (∀ i k, 0 ≤ v i k) ∧ (∀ i, ‖v i‖ = 1) ∧
      (∀ i j k, ‖v i - v j‖ ^ 2 ≤ ‖v i - v k‖ ^ 2 + ‖v k - v j‖ ^ 2) ∧
      (1 / ((faces X d).card : ℝ) ^ 2) * ∑ i, ∑ j, |inner ℝ (v i) (v j)| ≤
        (degree X d : ℝ) / (faces X d).card ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ A B : Finset (faces X d), Disjoint A B →
        β * (faces X d).card ≤ A.card → β * (faces X d).card ≤ B.card →
        ∃ i ∈ A, ∃ j ∈ B, ‖v i - v j‖ ^ 2 ≤ 2 / (β * Real.sqrt (α * d)) := by sorry

end SteurerHDX
