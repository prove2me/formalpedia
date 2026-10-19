-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_closureProperties
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.closureProperties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:04:37.340978+00:00
-- url     : https://prove2.me/theorems/5315a997-50fb-4a42-ada2-3b5e1241e5b0
-- title:
--   Proposition 4: hereditary, convex-closure and product properties
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   The following assertions hold, without requiring the initial sets to be convex:
--   $$
--   A\text{ is }\mu\text{-compact}\Longrightarrow
--   \begin{cases}
--   B\text{ is }\mu\text{-compact},&B\subseteq A\text{ closed},\\
--   \overline{\operatorname{co}}A\text{ is }\mu\text{-compact}.&
--   \end{cases}
--   $$
--   Every finite or countable product of source-admissible $\mu$-compact sets is $\mu$-compact in the product topology. Moreover, for every source-admissible $A$, $b:M(A)\to\overline{\operatorname{co}}A$ is continuous, and compact $A$ is $\mu$-compact. Empty closed subsets and empty products are allowed.
--
--   These are the hereditary, hull, product and elementary compactness properties.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 4, Proposition 4: hereditary, convex-closure and product properties

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

/-- Proposition 4, PDF pp.5–6; the continuity and compact-domain assertions
of PDF p.4 are retained as additional clauses. No convexity of A or its closed
subsets is required. The countable product permits an empty index type. -/
theorem closureProperties (A : Set E) (hA : GeneralBarycenterSpace A) :
    (MuCompact A → ∀ B : Set E, B ⊆ A → IsClosed B → MuCompact B) ∧
    (MuCompact A → MuCompact (closedConvexHull ℝ A)) ∧
    (∀ (I : Type u) [Countable I] (V : I → Type u)
      [∀ i, UniformSpace (V i)] [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
      [∀ i, IsUniformAddGroup (V i)] [∀ i, ContinuousSMul ℝ (V i)]
      [∀ i, LocallyConvexSpace ℝ (V i)] [∀ i, T2Space (V i)]
      (B : ∀ i, Set (V i)),
      (∀ i, GeneralBarycenterSpace (B i)) → (∀ i, MuCompact (B i)) →
      MuCompact (Set.pi Set.univ B)) ∧
    Continuous (pettisBarycenter A) ∧
    (IsCompact A → MuCompact A) := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
