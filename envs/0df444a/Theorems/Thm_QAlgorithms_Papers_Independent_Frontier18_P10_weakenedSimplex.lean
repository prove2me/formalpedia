-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_weakenedSimplex
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.weakenedSimplex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:14:51.848336+00:00
-- url     : https://prove2.me/theorems/ab031820-bf04-4f1e-bf38-2934f17cf8f2
-- title:
--   Proposition 13: weakened-topology subprobability simplex
-- statement:
--   For every finite real $p>1$, in the norm topology of $\ell^p(\mathbb N)$ the subprobability simplex
--   $$\Delta_p=\{x:x_i\ge0,\ \sum_i x_i\le1\}$$
--   is pointwise $\mu$-compact but is not $\mu$-compact.
--
--   The coordinate-mass condition is distinct from the positive l^p unit part.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 12, Proposition 13: weakened-topology subprobability simplex

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section LpResults

/-- Proposition 13, PDF p.12: finite real p>1, expressed by finite ENNReal p.
The Fact binder only supplies the normed-space instance and follows from p>1. -/
theorem weakenedSimplex (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hfinite : p < ⊤) :
    PointwiseMuCompact (subprobabilitySimplex p) ∧
    ¬ MuCompact (subprobabilitySimplex p) := by sorry

end LpResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
