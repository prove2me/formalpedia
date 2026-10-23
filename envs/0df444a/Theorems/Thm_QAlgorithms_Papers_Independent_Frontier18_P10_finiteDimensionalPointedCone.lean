-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_finiteDimensionalPointedCone
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.finiteDimensionalPointedCone
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:19:12.267988+00:00
-- url     : https://prove2.me/theorems/97a6f34b-d3c9-4479-bd92-855c39b5ae02
-- title:
--   Lemma 3: finite-dimensional pointed cones
-- statement:
--   Let $d\ge0$ and let $C\subseteq\mathbb R^d$ be a closed convex cone containing $0$. Assume it is pointed:
--   $$x\in C,\ -x\in C\quad\Longrightarrow\quad x=0.$$
--   Then $C$ is generalized $\mu$-compact, meaning that finite convex decompositions with barycenter in any compact subset have uniformly nearly all their mass in one compact subset.
--
--   The zero cone and the zero-dimensional case are included; no boundedness is assumed.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 21, Lemma 3: finite-dimensional pointed cones

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

/-- Lemma 3, PDF p.21: closed convex pointed cones in real finite-dimensional
space are generalized µ-compact. The zero cone and d=0 are included. -/
theorem finiteDimensionalPointedCone (d : ℕ) (C : Set (Fin d → ℝ))
    (hclosed : IsClosed C) (hcone : IsPointedCone C) :
    GeneralizedMuCompact C := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P10

end
