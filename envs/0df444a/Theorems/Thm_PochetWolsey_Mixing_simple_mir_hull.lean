-- Prove2me | Theorems.Thm_PochetWolsey_Mixing_simple_mir_hull
-- name    : PochetWolsey.Mixing.simple_mir_hull
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:13.040198+00:00
-- url     : https://prove2.me/theorems/e03bd5e2-2757-4d82-a2ea-1b7107f140a9
-- title:
--   Proposition 8.1 — simple mixed-integer rounding and hull
-- statement:
--   Let $b\in\mathbb R$, $f=b-\lfloor b\rfloor$, and $X^{MI}=\{(s,y)\in\mathbb R_+\times\mathbb Z:s+y\ge b\}$. The simple mixed-integer rounding inequality is valid on $X^{MI}$, and the following system describes its convex hull:
--   $$
--   s\ge f(\lceil b\rceil-y)\quad\text{on }X^{MI},\qquad
--   \operatorname{conv}(X^{MI})=\{(s,y)\in\mathbb R^2:s+y\ge b,\ s+fy\ge f\lceil b\rceil,\ s\ge0\}.
--   $$
--   This scalar case provides the rounding constraint underlying the mixing inequalities.
--
--   **Formalization Note** Both parts of Proposition 8.1 are included. The integer variable is unrestricted, the hull is taken in real two-dimensional space, and integral or negative $b$ is allowed. When $f=0$, the rounding inequality is simply $s\ge0$.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 237 (PDF 251), Proposition 8.1, Eq. (8.1)

import Mathlib
import Definitions.Def_PochetWolsey_Mixing_Model

namespace PochetWolsey.Mixing

theorem simple_mir_hull (b : ℝ) :
    (∀ p ∈ basicSet b, frac b * ((⌈b⌉ : ℝ) - p.2) ≤ p.1) ∧
    convexHull ℝ (basicSet b) =
      {p : ℝ × ℝ | b ≤ p.1 + p.2 ∧
        frac b * (⌈b⌉ : ℝ) ≤ p.1 + frac b * p.2 ∧ 0 ≤ p.1} := by sorry

end PochetWolsey.Mixing
