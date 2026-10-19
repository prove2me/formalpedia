-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_probabilityMeasuresMuCompact
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.probabilityMeasuresMuCompact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:14:25.458984+00:00
-- url     : https://prove2.me/theorems/b5f0ea08-8e3c-41ea-a391-56c5191feaad
-- title:
--   Corollary 4: probability measures form a µ-compact set
-- statement:
--   For every complete separable metric space $X$, the set of all Borel probability measures is $\mu$-compact in weak convergence:
--   $$M(X)\text{ is }\mu\text{-compact}.$$
--   It is realized as a subset of the weak locally convex real space of signed finite measures, using integration against bounded continuous real functions.
--
--   This supplies the measure-space example with its actual affine structure.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 11, Corollary 4: probability measures form a µ-compact set

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

/-- Corollary 4, PDF p.11: all probability measures are µ-compact in the
weak topology, using a concrete linear ambient rather than variation norm. -/
theorem probabilityMeasuresMuCompact {Z : Type u} [MetricSpace Z]
    [CompleteSpace Z] [SeparableSpace Z] : MuCompact (weakProbabilitySet Z) := by sorry

end WeakMeasures

end QAlgorithms.Papers.Independent.Frontier18.P10

end
