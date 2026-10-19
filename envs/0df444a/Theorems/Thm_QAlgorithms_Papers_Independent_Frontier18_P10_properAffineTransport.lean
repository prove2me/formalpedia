-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_properAffineTransport
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.properAffineTransport
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:04:13.726333+00:00
-- url     : https://prove2.me/theorems/1cb8ea37-1140-4eb6-be5f-99836bab00af
-- title:
--   Proposition 3: proper affine maps
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   Let $B$ satisfy the same standing conditions in another Hausdorff locally convex real space. Assume $A,B$ are convex and $\phi:A\to B$ is continuous and affine, with compact inverse images of compact subsets of $B$. Then
--   $$\mu\text{-compactness of }B\Longrightarrow\mu\text{-compactness of }A.$$
--   If $\phi$ is onto, also
--   $$\mu\text{-compactness of }A\Longrightarrow\mu\text{-compactness of }B.$$
--
--
--   This gives both directions of transport under proper affine maps.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 5, Proposition 3: proper affine maps

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

/-- Proposition 3, PDF p.5 (including footnote 2 for B): both directions of
proper affine transport, with surjectivity needed only for the second. -/
theorem properAffineTransport {F : Type v} [UniformSpace F] [AddCommGroup F]
    [Module ℝ F] [IsUniformAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F]
    (A : Set E) (B : Set F) (hA : GeneralBarycenterSpace A)
    (hB : GeneralBarycenterSpace B) (hcA : Convex ℝ A) (hcB : Convex ℝ B)
    (phi : E → F) (hcont : ContinuousOn phi A) (haff : AffineOnSet A phi)
    (hmap : MapsTo phi A B)
    (hproper : ∀ C : Set F, C ⊆ B → IsCompact C →
      IsCompact {x ∈ A | phi x ∈ C}) :
    (MuCompact B → MuCompact A) ∧
    ((∀ y ∈ B, ∃ x ∈ A, phi x = y) → MuCompact A → MuCompact B) := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
