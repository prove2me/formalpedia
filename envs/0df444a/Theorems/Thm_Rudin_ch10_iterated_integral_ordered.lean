-- Prove2me | Theorems.Thm_Rudin_ch10_iterated_integral_ordered
-- name    : Rudin.ch10_iterated_integral_ordered
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T04:38:19.365015+00:00
-- url     : https://prove2.me/theorems/cafd03f2-cba5-425e-9487-1ee8d16abb32
-- title:
--   Theorem 10.2 — the order of integration is immaterial (ordered endpoints)
-- statement:
--   Let $[a,b]\times[c,d]\subseteq\mathbb{R}^2$ be a 2-cell, so that $a\le b$ and $c\le d$, and let $f$ be a real function that is continuous on this rectangle. Then the two iterated integrals of $f$ agree:
--
--   $$\int_a^b\!\!\left(\int_c^d f(x,y)\,dy\right)dx\;=\;\int_c^d\!\!\left(\int_a^b f(x,y)\,dx\right)dy .$$
--
--   This is Rudin's Theorem 10.2, which he states for 2-cells; in his Definition 10.1 a $k$-cell carries the ordering conditions $a_i\le b_i$ on its edges. The ordering hypotheses are essential for the formalized version above, because the interval integrals are oriented: if $a>b$ the rectangle $[a,b]\times[c,d]$ is empty, the continuity hypothesis becomes vacuous, and the resulting statement — an unrestricted interchange of iterated integrals for arbitrary functions — is false.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, p. 246, Definition 10.1 and Theorem 10.2

import Mathlib

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 10.2: for a continuous function on a 2-cell the two iterated integrals agree;
the order of integration is immaterial.  The ordering hypotheses `a ≤ b` and `c ≤ d` are part of
Rudin's definition of a 2-cell and are needed here: without them the continuity hypothesis is
vacuous while the oriented interval integrals still range over a nondegenerate interval. -/
theorem ch10_iterated_integral_ordered (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d)) :
    (∫ x in a..b, ∫ y in c..d, f x y) = ∫ y in c..d, ∫ x in a..b, f x y := by sorry

end Rudin
