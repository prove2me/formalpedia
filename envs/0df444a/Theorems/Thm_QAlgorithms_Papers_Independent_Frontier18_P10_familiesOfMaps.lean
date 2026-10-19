-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_familiesOfMaps
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.familiesOfMaps
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:05:25.043722+00:00
-- url     : https://prove2.me/theorems/000d546a-e4de-47e6-844c-4d600668d7d6
-- title:
--   Corollary 1: families of maps
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   Let $F$ be a Hausdorff locally convex real space of maps from a set $X$ into a Hausdorff locally convex real space $Y$. Let $F_0\subseteq F$ be convex, closed, bounded, complete, separable and metrizable, and suppose all its maps take values in a convex $\mu$-compact source-admissible $A\subseteq Y$. Suppose some $x_0\in X$ has sequentially continuous evaluation on $F_0$, and
--   $$\{\Phi\in F_0:\Phi(x_0)\in C\}\text{ is relatively compact}$$
--   for every compact $C\subseteq A$. Then $F_0$ is $\mu$-compact.
--
--   This criterion applies proper affine transport to evaluation at one point.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 6, Corollary 1: families of maps

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

/-- Corollary 1, PDF p.6: the ambient locally convex space is represented
as a linear space of maps by an injective linear realization. Only sequential
continuity of evaluation at x0 and relatively compact evaluation preimages
are assumed. No compactness of each fiber is an input hypothesis. -/
theorem familiesOfMaps {X : Type v} {Y : Type w}
    [UniformSpace Y] [AddCommGroup Y] [Module ℝ Y] [IsUniformAddGroup Y]
    [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] [T2Space Y]
    (realize : E →ₗ[ℝ] (X → Y)) (hinj : Function.Injective realize)
    (F0 : Set E) (hF0 : GeneralBarycenterSpace F0) (hcF0 : Convex ℝ F0)
    (A : Set Y) (hA : GeneralBarycenterSpace A) (hcA : Convex ℝ A)
    (hmA : MuCompact A) (hvalues : ∀ f ∈ F0, ∀ x, realize f x ∈ A)
    (x0 : X)
    (hseq : ∀ (f : ℕ → F0) (f0 : F0), Tendsto f atTop (𝓝 f0) →
      Tendsto (fun n => realize (f n) x0) atTop (𝓝 (realize f0 x0)))
    (hrel : ∀ C : Set Y, C ⊆ A → IsCompact C →
      IsCompact (closure {f ∈ F0 | realize f x0 ∈ C})) :
    MuCompact F0 := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
