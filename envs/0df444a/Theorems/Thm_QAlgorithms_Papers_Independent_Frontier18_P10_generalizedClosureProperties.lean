-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_generalizedClosureProperties
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.generalizedClosureProperties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:18:50.717979+00:00
-- url     : https://prove2.me/theorems/3cbb38ea-308d-4a43-8739-8f08a9025dd3
-- title:
--   Unnumbered closure properties of generalized µ-compactness
-- statement:
--   For a closed convex set $A$ in a Hausdorff real topological vector space, call $A$ generalized $\mu$-compact when every compact $K\subseteq A$ and $\varepsilon>0$ admit compact $L\subseteq A$ such that every finite normalized convex decomposition with barycenter in $K$ assigns mass at least $1-\varepsilon$ to $L$:
--   $$\sum_{i:x_i\in L}\lambda_i\ge1-\varepsilon.$$
--   Nonempty finite or countable intersections, finite or countable products (including the empty product), and closed convex subsets preserve this property. If a continuous affine map $A\to B$ has compact inverse images of compact sets, generalized $\mu$-compactness of $B$ implies that of $A$; if the map is onto, the converse also holds. On the closed convex bounded source-admissible class,
--   $$\mu\text{-compactness}\iff\text{generalized }\mu\text{-compactness}.$$
--
--
--   This formulation applies to unbounded domains without an all-probability barycenter map.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 20, Unnumbered closure properties of generalized µ-compactness

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

/-- §5, PDF pp.20–21: generalized closure properties and proper affine
transport, together with equivalence to ordinary µ-compactness on the bounded
admissible class. An empty product is allowed; an empty intersection is excluded. -/
theorem generalizedClosureProperties (E : Type u) [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [T2Space E] :
    (∀ (I : Type u) [Countable I] (B : I → Set E),
      (∀ i, GeneralizedMuCompact (B i)) → Nonempty I →
      GeneralizedMuCompact (⋂ i, B i)) ∧
    (∀ (I : Type u) [Countable I] (V : I → Type u)
      [∀ i, TopologicalSpace (V i)] [∀ i, AddCommGroup (V i)]
      [∀ i, Module ℝ (V i)] [∀ i, IsTopologicalAddGroup (V i)]
      [∀ i, ContinuousSMul ℝ (V i)] [∀ i, T2Space (V i)]
      (B : ∀ i, Set (V i)),
      (∀ i, GeneralizedMuCompact (B i)) →
      GeneralizedMuCompact (Set.pi Set.univ B)) ∧
    (∀ A : Set E, GeneralizedMuCompact A →
      ∀ B : Set E, B ⊆ A → Convex ℝ B → IsClosed B → GeneralizedMuCompact B) ∧
    (∀ (F : Type v) [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
      [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F]
      (A : Set E) (B : Set F), Convex ℝ A → IsClosed A → Convex ℝ B → IsClosed B →
      ∀ phi : E → F, ContinuousOn phi A → AffineOnSet A phi → MapsTo phi A B →
      (∀ C : Set F, C ⊆ B → IsCompact C → IsCompact {x ∈ A | phi x ∈ C}) →
      (GeneralizedMuCompact B → GeneralizedMuCompact A) ∧
      ((∀ y ∈ B, ∃ x ∈ A, phi x = y) →
        GeneralizedMuCompact A → GeneralizedMuCompact B)) ∧
    (∀ (F : Type v) [UniformSpace F] [AddCommGroup F] [Module ℝ F]
      [IsUniformAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
      (A : Set F), GeneralBarycenterSpace A → Convex ℝ A →
      (MuCompact A ↔ GeneralizedMuCompact A)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P10

end
