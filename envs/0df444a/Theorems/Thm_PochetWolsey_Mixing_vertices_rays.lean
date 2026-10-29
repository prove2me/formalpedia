-- Prove2me | Theorems.Thm_PochetWolsey_Mixing_vertices_rays
-- name    : PochetWolsey.Mixing.vertices_rays
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:49.347522+00:00
-- url     : https://prove2.me/theorems/1650943d-86e5-43c6-80c4-b940196519c7
-- title:
--   Proposition 8.3 — extreme points and rays of the mixing hull
-- statement:
--   Let $K>0$, $b\in\mathbb R^K$, and $P=\operatorname{conv}(X^{MIX}_K(b))$. Put $f_0=0$, $f_j=b_j-\lfloor b_j\rfloor$, and
--   $$
--   v^j=(f_j,(\lceil b_k-f_j\rceil)_{k=1}^K),\qquad r^0=(1,-\mathbf1),\qquad r^k=(0,e_k).
--   $$
--   The extreme points of $P$ are exactly the points $v^j$, for $0\le j\le K$. A direction is an extreme-ray direction of $P$ if and only if it is a positive multiple of one of $r^0,r^1,\ldots,r^K$. This identifies both the bounded and recession components relevant to the extended formulation.
--
--   **Formalization Note** The book lists ray representatives; the statement includes all their positive multiples. The extreme-point conclusion is equality of sets, allowing repeated entries in the displayed family. No ordering, positivity, or distinctness of the fractional parts is assumed.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 242 (PDF 256), Proposition 8.3

import Mathlib
import Definitions.Def_PochetWolsey_Mixing_Geometry

namespace PochetWolsey.Mixing

theorem vertices_rays {K : ℕ} (hK : 0 < K) (b : Fin K → ℝ) :
    (∀ d : Point K, IsExtremeRay (convexHull ℝ (mixingSet b)) d ↔
      ∃ j : Option (Fin K), ∃ a : ℝ, 0 < a ∧ d = a • ray j) ∧
    Set.extremePoints ℝ (convexHull ℝ (mixingSet b)) = Set.range (vertex b) := by sorry

end PochetWolsey.Mixing
