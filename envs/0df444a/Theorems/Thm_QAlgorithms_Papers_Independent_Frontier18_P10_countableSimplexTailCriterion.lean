-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_countableSimplexTailCriterion
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.countableSimplexTailCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:10:57.893382+00:00
-- url     : https://prove2.me/theorems/4da2dc78-0d03-409d-a598-d3fda039cac0
-- title:
--   Remark 2: countable-simplex tightness criterion
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   Let $(e_i)_{i\ge0}$ be a closed discrete family of isolated extreme points generating the convex set $A$ by closed convex hull. Assume this is a simplex presentation: the barycenter map on probabilities on $\{e_i\}$ is injective. Then $A$ is $\mu$-compact exactly when for every compact $K\subseteq A$ and $\varepsilon>0$, some $n\in\mathbb N$ satisfies
--   $$\sum_i\pi_i e_i\in K,\quad \pi_i\ge0,\quad\sum_i\pi_i=1
--   \quad\Longrightarrow\quad\sum_{i\ge n}\pi_i<\varepsilon.$$
--   All displayed vector sums converge.
--
--   This is the tail criterion for the source’s concrete countably generated simplex, without a countability assertion for arbitrary simplexes.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 6, Remark 2: countable-simplex tightness criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section LocallyConvexResults

variable {E : Type u} [UniformSpace E] [AddCommGroup E] [Module ℝ E]
    [hgroup : IsUniformAddGroup E] [hsmul : ContinuousSMul ℝ E]
    [hlc : LocallyConvexSpace ℝ E] [hhaus : T2Space E]

include hgroup hsmul hlc hhaus

/-- Remark 2, PDF p.6: the tail criterion for an actual countable,
closed discrete family of isolated extreme points generating a simplex.
The barycenter injectivity expresses uniqueness on this boundary; it does not
postulate a countable extreme decomposition for arbitrary µ-compact sets.
Nat indexing uses the tail after the first n coordinates. -/
theorem countableSimplexTailCriterion (A : Set E)
    (hA : GeneralBarycenterSpace A) (hc : Convex ℝ A) (e : ℕ → E)
    (he : Topology.IsClosedEmbedding e) (hext : Set.range e ⊆ A.extremePoints ℝ)
    (hgen : closedConvexHull ℝ (Set.range e) = A)
    (hsimplex : Function.Injective (pettisBarycenter (Set.range e))) :
    MuCompact A ↔
      ∀ K : Set E, K ⊆ A → IsCompact K → ∀ epsilon : ℝ, 0 < epsilon →
        ∃ n : ℕ, ∀ weight : ℕ → ℝ,
          (∀ i, 0 ≤ weight i) → HasSum weight 1 →
          ∀ x ∈ K, HasSum (fun i => weight i • e i) x →
            (∑' i, if n ≤ i then ENNReal.ofReal (weight i) else 0) <
              ENNReal.ofReal epsilon := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
