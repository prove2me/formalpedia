-- Prove2me | Theorems.Thm_PochetWolsey_Capacities_intersection_hull
-- name    : PochetWolsey.Capacities.intersection_hull
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:08.001792+00:00
-- url     : https://prove2.me/theorems/23c52396-5bd5-4d61-a9e0-0dcd477755df
-- title:
--   Theorem 9.8 — intersecting constant-capacity lot-sizing hulls
-- statement:
--   Let $n\ge1$, let $C>0$ be a constant capacity, and let the preprocessed demands satisfy $0\le d_t\le C$. Work in the common stock/setup space $\mathbb R^{n+1}\times\mathbb R^n$. Define
--   $$
--   X^{\mathrm{WW-CC}}=\left\{(s,y)\in\mathbb R_+^{n+1}\times\{0,1\}^n:s_{k-1}+C\sum_{u=k}^t y_u\ge\sum_{u=k}^t d_u\quad(1\le k\le t\le n)\right\}.
--   $$
--   For each $k=1,\ldots,n$, define $X_k^{\mathrm{DLSI-CC}}$ in that same space by imposing the same nonnegativity and binary conditions and only the covering inequalities for that fixed $k$. Then
--   $$
--   \operatorname{conv}(X^{\mathrm{WW-CC}})=\bigcap_{k=1}^n\operatorname{conv}(X_k^{\mathrm{DLSI-CC}}).
--   $$
--   The assertion identifies the full Wagner–Whitin feasible hull with the intersection of its individual initial-stock hulls.
--
--   **Formalization Note** All $n+1$ stock coordinates are retained in every component, including the terminal stock, and neither endpoint is fixed to zero. Periods are zero-based in Lean; `k.castSucc` selects the stock before that period. The theorem is a feasible-set identity and has no cost or optimization-value parameters. The sets on both sides are given by the original constraints, independently of the claimed equality.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, p. 283 (PDF 296), Theorem 9.8

import Mathlib
import Definitions.Def_PochetWolsey_Capacities_Model

namespace PochetWolsey.Capacities

/-- Theorem 9.8. All sets are in the same full stock/setup space. -/
theorem intersection_hull {n : ℕ} (hn : 0 < n) (C : ℝ) (hC : 0 < C)
    (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t ∧ d t ≤ C) :
    convexHull ℝ
      {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) |
        (∀ j, 0 ≤ p.1 j) ∧ (∀ u, p.2 u = 0 ∨ p.2 u = 1) ∧
        ∀ k t, k ≤ t → (∑ u ∈ Finset.Icc k t, d u) ≤
          p.1 k.castSucc + C * ∑ u ∈ Finset.Icc k t, p.2 u} =
    ⋂ k : Fin n, convexHull ℝ
      {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) |
        (∀ j, 0 ≤ p.1 j) ∧ (∀ u, p.2 u = 0 ∨ p.2 u = 1) ∧
        ∀ t, k ≤ t → (∑ u ∈ Finset.Icc k t, d u) ≤
          p.1 k.castSucc + C * ∑ u ∈ Finset.Icc k t, p.2 u} := by sorry

end PochetWolsey.Capacities
