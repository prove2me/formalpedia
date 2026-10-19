-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_boundedFiniteMeasuresMuCompact
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.boundedFiniteMeasuresMuCompact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:13:51.446989+00:00
-- url     : https://prove2.me/theorems/7aca54ef-aca8-43f6-9167-e21a12af524c
-- title:
--   Proposition 10: finite Borel measure sets
-- statement:
--   Let $X$ be a complete separable metric space and $M$ a weakly closed set of finite nonnegative Borel measures on $X$. Suppose there is a finite real $C$ such that $\mu(X)\le C$ for every $\mu\in M$. Then
--   $$M\text{ is }\mu\text{-compact in the weak convergence topology}.$$
--   The affine ambient is the real span of integration coordinates against bounded continuous functions.
--
--   Convexity of $M$ is not assumed; signed elements are used only for the linear ambient.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 11, Proposition 10: finite Borel measure sets

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

/-- Proposition 10, PDF p.11: weakly closed sets of nonnegative finite
Borel measures with one uniform finite mass bound. Convexity is not required. -/
theorem boundedFiniteMeasuresMuCompact {Z : Type u} [MetricSpace Z]
    [CompleteSpace Z] [SeparableSpace Z] (M : Set (FiniteMeasure Z))
    (hclosed : IsClosed M)
    (hmass : ∃ C : ℝ, ∀ mu ∈ M, (mu : Measure Z) Set.univ ≤ ENNReal.ofReal C) :
    MuCompact (weakFiniteMeasure '' M) := by sorry

end WeakMeasures

end QAlgorithms.Papers.Independent.Frontier18.P10

end
