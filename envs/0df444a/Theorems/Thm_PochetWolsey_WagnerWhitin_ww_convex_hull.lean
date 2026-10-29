-- Prove2me | Theorems.Thm_PochetWolsey_WagnerWhitin_ww_convex_hull
-- name    : PochetWolsey.WagnerWhitin.ww_convex_hull
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:51.897628+00:00
-- url     : https://prove2.me/theorems/8897fedf-a42e-404b-ba80-447d2ca59771
-- title:
--   Theorem 7.10 — the Wagner–Whitin convex hull
-- statement:
--   Let $n\ge1$ and let $d_t\ge0$ be real demands. Define $P^{WW-U}$ directly by
--   $$s\in\mathbb R_+^{n+1},\quad y\in[0,1]^n,\qquad s_{k-1}\ge\sum_{j=k}^l d_j\Bigl(1-\sum_{u=k}^j y_u\Bigr)\quad(1\le k\le l\le n).$$
--   Let $X^{WW-U}$ be the subset where $y$ is integral. Then:
--
--   1. For every holding-cost vector $h\ge0$ and arbitrary real setup costs $q$, any optimal extreme point of $\min\{hs+qy:(s,y)\in P^{WW-U}\}$ belongs to $X^{WW-U}$ and minimizes the same objective over $X^{WW-U}$, hence solves the formulation (7.29)–(7.32) of $WW-U$.
--   2. Independently of costs,
--   $$P^{WW-U}=\operatorname{conv}(X^{WW-U}).$$
--
--   The result identifies a compact exact hull and its optimization consequence. It does not require stock to take integer values when demand is real.
--
--   **Formalization Note** Initial stock $s_0$ remains a decision variable, and terminal stock $s_n$ has only its nonnegativity constraint. The stock inequalities, integer restriction and objective are local definitions inside this theorem so that its solo blind audit receives their complete code. Neither stock minimality nor integrality is assumed. Only clause (i) quantifies holding and setup costs.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 225 (PDF 239), Theorem 7.10 and Eqs. (7.29)–(7.32); proof pp. 230–231 (PDF 244–245)

import Mathlib

open scoped BigOperators

namespace PochetWolsey.WagnerWhitin

theorem ww_convex_hull (n : ℕ) (hn : 0 < n)
    (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) :
    let P : Set ((Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
      {z | (∀ t, 0 ≤ z.1 t) ∧ (∀ t, 0 ≤ z.2 t ∧ z.2 t ≤ 1) ∧
        ∀ k l : Fin n, k ≤ l →
          z.1 k.castSucc ≥ ∑ j ∈ Finset.Icc k l,
            d j * (1 - ∑ u ∈ Finset.Icc k j, z.2 u)}
    let X : Set ((Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
      {z | z ∈ P ∧ ∀ t, ∃ a : ℤ, z.2 t = (a : ℝ)}
    let cost := fun (h : Fin (n + 1) → ℝ) (q : Fin n → ℝ)
      (z : (Fin (n + 1) → ℝ) × (Fin n → ℝ)) =>
        (∑ t, h t * z.1 t) + ∑ t, q t * z.2 t
    (∀ (h : Fin (n + 1) → ℝ) (q : Fin n → ℝ), (∀ t, 0 ≤ h t) →
      ∀ z, z ∈ P.extremePoints ℝ →
        (∀ w ∈ P, cost h q z ≤ cost h q w) →
          z ∈ X ∧ ∀ w ∈ X, cost h q z ≤ cost h q w) ∧
    P = convexHull ℝ X := by sorry

end PochetWolsey.WagnerWhitin
