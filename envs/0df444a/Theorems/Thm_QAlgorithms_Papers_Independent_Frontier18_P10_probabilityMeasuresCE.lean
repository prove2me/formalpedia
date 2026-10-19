-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_probabilityMeasuresCE
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.probabilityMeasuresCE
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:17:57.821231+00:00
-- url     : https://prove2.me/theorems/6f43d0b1-9af8-4ec0-beb6-0496920fc44d
-- title:
--   Corollary 5: all CE properties of probability measures
-- statement:
--   Let $X$ be a complete separable metric space and let $A=M(X)$ be its Borel probability measures with weak convergence and the natural affine structure. Then
--   $$\mathrm{(i)},\ \mathrm{(ii)},\ \mathrm{(iii)},\ \mathrm{(iv)},\ \mathrm{(v)}$$
--   of Theorem 1 all hold: midpoint mixing is open; the full barycenter map and the barycenter map on $M(\overline{\operatorname{extr}A})$ are open; and convex hulls of all bounded continuous real functions, and of all such concave functions, are continuous.
--
--   All five properties are retained in the weak signed-measure ambient.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 16, Corollary 5: all CE properties of probability measures

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

/-- Corollary 5, PDF p.16: all five CE properties, including openness of
the full and closed-extreme-boundary barycenter maps. -/
theorem probabilityMeasuresCE {Z : Type u} [MetricSpace Z]
    [CompleteSpace Z] [SeparableSpace Z] :
    let A := weakProbabilitySet Z
    StableConvexSet A ∧ BarycenterOpen A A ∧
    BarycenterOpen A (closure (A.extremePoints ℝ)) ∧
    StrongCEProperty A ∧ CEProperty A := by sorry

end WeakMeasures

end QAlgorithms.Papers.Independent.Frontier18.P10

end
