-- Prove2me | Theorems.Thm_ShapeSOS_ConvexConsistency_geometric_psd
-- name    : ShapeSOS.ConvexConsistency.geometric_psd
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:22:34.98742+00:00
-- url     : https://prove2.me/theorems/d552fdc1-7112-4717-b4aa-95a278445a80
-- title:
--   Lemma 3.6 — positive semidefiniteness of the geometric band matrix
-- statement:
--   Let $n\ge1$ and $a_1>a_n>0$. Intermediate entries are $a_i=a_1(a_n/a_1)^{(i-1)/(n-1)}$. Let $M$ have diagonal entries $a_i/2$ for $i\in\{1,2,n-1,n\}$ and $a_i$ for $3\le i\le n-2$, and let $M_{i-1,i+1}=M_{i+1,i-1}=-a_i/2$ for $2\le i\le n-1$. All other entries are zero. Then
--   $$M\succeq0.$$
--   Endpoint overlap at small sizes is interpreted literally. The $n=2$ matrix is diagonal with positive entries. At $n=1$ the two endpoints are the same entry, so the strict endpoint inequality is impossible, exactly as in the source.
--
--   Differences from the source:
--   - encoding: real finite-dimensional coordinates and Euclidean geometry → Fin n → ℝ with its usual topology and explicit norm₂ = sqrt(sum x_i²); reason: the topology is the Euclidean topology and all numerical distances use the Euclidean norm
--   - encoding: one-based geometric sequence with endpoints a_1 and a_n → zero-based Fin n entries, Real.rpow, and n=1 implies first=last; reason: the compatibility condition expresses that two names for the same endpoint agree; it excludes no compatible source instance
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, p. 9, Lemma 3.6

import Definitions.Def_ShapeSOS_ConvexConsistency_Algebra

set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators Topology MeasureTheory

namespace ShapeSOS.ConvexConsistency

theorem geometric_psd (n : ℕ) (hn : 0 < n) (first last : ℝ)
    (hfirst : last < first) (hlast : 0 < last)
    (hendpoint : n = 1 → first = last) :
    (geometricMatrix n first last).PosSemidef := by sorry

end ShapeSOS.ConvexConsistency
