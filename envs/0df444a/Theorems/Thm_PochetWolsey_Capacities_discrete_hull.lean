-- Prove2me | Theorems.Thm_PochetWolsey_Capacities_discrete_hull
-- name    : PochetWolsey.Capacities.discrete_hull
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:01.213098+00:00
-- url     : https://prove2.me/theorems/fdae2afc-d6fe-47a0-90c5-e8500a1aaa0c
-- title:
--   Theorem 9.3 — discrete constant-capacity lot-sizing hull
-- statement:
--   Let $n\ge1$, $C>0$, and $0\le d_t\le C$ for $1\le t\le n$. Write $d_{1t}=\sum_{u=1}^t d_u$, and assume the discrete lot-sizing feasible set $X^{\mathrm{DLS-CC}}$ is nonempty.
--
--   Then the original binary covering set has the exact convex-hull description
--   $$
--   \operatorname{conv}(X^{\mathrm{DLS-CC}})=\left\{y\in[0,1]^n:\sum_{u=1}^t y_u\ge\left\lceil\frac{d_{1t}}C\right\rceil\quad(1\le t\le n)\right\}.
--   $$
--   Thus rounded prefix inequalities and the setup bounds describe the entire hull.
--
--   **Formalization Note** The left-hand set is written explicitly using $C\sum_{u=1}^t y_u\ge d_{1t}$ and binary setups. The hull is the ordinary real convex hull, without a closure operation.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, p. 276 (PDF 289), Theorem 9.3

import Mathlib
import Definitions.Def_PochetWolsey_Capacities_Model

namespace PochetWolsey.Capacities

/-- Theorem 9.3, with both sets expanded from their original constraints. -/
theorem discrete_hull {n : ℕ} (hn : 0 < n) (C : ℝ) (hC : 0 < C)
    (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t ∧ d t ≤ C)
    (hfeas : ({y : Fin n → ℝ | (∀ u, y u = 0 ∨ y u = 1) ∧
      ∀ t, (∑ u ∈ Finset.Iic t, d u) ≤ C * ∑ u ∈ Finset.Iic t, y u} : Set _).Nonempty) :
    convexHull ℝ {y : Fin n → ℝ | (∀ u, y u = 0 ∨ y u = 1) ∧
      ∀ t, (∑ u ∈ Finset.Iic t, d u) ≤ C * ∑ u ∈ Finset.Iic t, y u} =
    {y : Fin n → ℝ | (∀ u, 0 ≤ y u ∧ y u ≤ 1) ∧
      ∀ t, (⌈(∑ u ∈ Finset.Iic t, d u) / C⌉ : ℤ) ≤
        (∑ u ∈ Finset.Iic t, y u)} := by sorry

end PochetWolsey.Capacities
