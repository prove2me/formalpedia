-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_positiveLpNotPointwise
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.positiveLpNotPointwise
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:15:37.927355+00:00
-- url     : https://prove2.me/theorems/7f87ced1-783c-47df-8b6b-30c5069b10e3
-- title:
--   Proposition 15: positive ℓ^p unit parts fail pointwise compactness
-- statement:
--   For every finite real $p>1$, the positive closed unit part in $\ell^p(\mathbb N)$,
--   $$A_p=\{x:x_i\ge0\text{ for all }i,\ \|x\|_p\le1\},$$
--   is not pointwise $\mu$-compact.
--
--   The countably infinite coordinate index and the stronger pointwise failure are retained.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 13, Proposition 15: positive ℓ^p unit parts fail pointwise compactness

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

/-- Proposition 15, PDF p.13: failure of pointwise µ-compactness, stronger
than merely failure of µ-compactness. The coordinate index is infinite. -/
theorem positiveLpNotPointwise (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 1 < p) (hfinite : p < ⊤) :
    ¬ PointwiseMuCompact (positiveLpUnitPart p) := by sorry

end LpResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
