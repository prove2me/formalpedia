-- Prove2me | Theorems.Thm_PochetWolsey_Modes_single_startup_hull
-- name    : PochetWolsey.Modes.single_startup_hull
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:08.019019+00:00
-- url     : https://prove2.me/theorems/1384c727-aaa4-48c7-b794-deabeaff2e36
-- title:
--   Proposition 12.4 — single-setup startup hull
-- statement:
--   Let $Y^{M1-SC}$ be the binary one-setup model with exact startups between adjacent periods. Its convex hull is the set of unit-box pairs $(y,z)$ satisfying one setup per period and
--   $$z_i(t)\ge y_i(t+1)-y_i(t),\qquad z_i(t)\le y_i(t+1),$$
--   $$z_i(t)+\sum_{j\ne i}(y_j(t+1)-z_j(t))\le1-y_i(t).$$
--   Thus $\operatorname{conv}(Y^{M1-SC})=P_{\mathrm{startup}}$. This eliminates the off-diagonal changeover variables while keeping the exact hull.
--
--   **Formalization Note** The graph has $n+1$ periods $0,\ldots,n$ and $n$ internal transitions. A transition index $t$ connects periods $t$ and $t+1$ and stores the book’s changeover or startup at the latter period. No transition into the first period is recorded, consistently with (12.2)–(12.3), which apply only from the second period onward. There are $m+1$ labels including idle label $0$.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 377 (PDF 388), Proposition 12.4, pp. 377–378 (PDF 388–389)

import Mathlib

namespace PochetWolsey.Modes

theorem single_startup_hull (m n : ℕ) :
    convexHull ℝ ({p : (Fin (m + 1) → Fin (n + 1) → ℝ) × (Fin (m + 1) → Fin n → ℝ) | (∀ i, (∀ t, p.1 i t = 0 ∨ p.1 i t = 1)) ∧ (∀ i, (∀ t, p.2 i t = 0 ∨ p.2 i t = 1)) ∧
    (∀ t, ∑ i, p.1 i t = 1) ∧
    (∀ i t, p.2 i t ≥ p.1 i t.succ - p.1 i t.castSucc ∧
      p.2 i t ≤ p.1 i t.succ ∧ p.2 i t ≤ 1 - p.1 i t.castSucc)}) =
    {p | (∀ i, (∀ t, 0 ≤ p.1 i t ∧ p.1 i t ≤ 1)) ∧ (∀ i, (∀ t, 0 ≤ p.2 i t ∧ p.2 i t ≤ 1)) ∧
    (∀ t, ∑ i, p.1 i t = 1) ∧
    (∀ i t, p.2 i t ≥ p.1 i t.succ - p.1 i t.castSucc ∧
      p.2 i t ≤ p.1 i t.succ ∧
      p.2 i t + ∑ j ∈ Finset.univ.erase i, (p.1 j t.succ - p.2 j t)
        ≤ 1 - p.1 i t.castSucc)} := by sorry

end PochetWolsey.Modes
