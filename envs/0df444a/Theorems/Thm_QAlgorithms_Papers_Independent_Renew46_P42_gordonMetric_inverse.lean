-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_gordonMetric_inverse
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.gordonMetric_inverse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:24:44.761498+00:00
-- url     : https://prove2.me/theorems/57ad274a-d1eb-40b7-af27-86e9b96def8f
-- title:
--   The covariant Gordon metric is the inverse metric
-- statement:
--   Let $c>0$, $n\ge1$ and $|\mathbf u|<c$. With $\eta=\operatorname{diag}(1,-1,-1,-1)$, $U=\gamma(1,\mathbf u/c)$, and $U_\flat=\eta U$, construct $G=\eta+(n^2-1)UU^T$ and $g=\eta+(n^{-2}-1)U_\flat U_\flat^T$. Then
--
--   $$U^T\eta U=1,\qquad gG=Gg=I.$$
--
--   This distinguishes the inverse Gordon metric from lowering indices with the Minkowski metric.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 5, §III C, (42)–(43): inverse Gordon metric

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.5, (42)–(43): both Gordon inverse identities, with eta-normalized flow. -/
theorem gordonMetric_inverse (c n : ℝ) (u : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) :
    quadratic minkowskiMetric (fourFlow c u) = 1 ∧
    gDown c n u * gUp c n u = 1 ∧ gUp c n u * gDown c n u = 1 := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
