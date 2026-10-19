-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_diracImageExample
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.diracImageExample
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:12:20.410772+00:00
-- url     : https://prove2.me/theorems/31b84889-fb1a-4b68-81db-96187c5c2fdc
-- title:
--   Remark 2: µ-compactness is not purely topological
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   Suppose $A$ is convex and not $\mu$-compact. In the weak linear ambient of signed finite measures on $A$, let $D=\{\delta_x:x\in A\}$. Then
--   $$D\text{ is }\mu\text{-compact},\qquad A\longrightarrow D,\quad x\longmapsto\delta_x,\text{ is a homeomorphism}.$$
--
--
--   The Dirac image is allowed to be nonconvex, illustrating dependence on affine structure.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 6, Remark 2: µ-compactness is not purely topological

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section WeakMeasures

variable {X : Type u} [TopologicalSpace X]

/-- Remark 2, PDF p.6: for a non-µ-compact convex admissible A, its Dirac
image is µ-compact and the natural Dirac map is a homeomorphism onto that image.
The two sets have different inherited convex structures. -/
theorem diracImageExample {E : Type u} [UniformSpace E] [AddCommGroup E]
    [Module ℝ E] [IsUniformAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    (A : Set E) (hA : GeneralBarycenterSpace A) (hc : Convex ℝ A)
    (hnot : ¬ MuCompact A) :
    MuCompact (Set.range (diracPoint (X := A))) ∧
    ∃ e : A ≃ₜ Set.range (diracPoint (X := A)),
      ∀ x, (e x).val = diracPoint x := by sorry

end WeakMeasures

end QAlgorithms.Papers.Independent.Frontier18.P10

end
