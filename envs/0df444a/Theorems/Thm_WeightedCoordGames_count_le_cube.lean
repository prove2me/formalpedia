-- Prove2me | Theorems.Thm_WeightedCoordGames_count_le_cube
-- name    : WeightedCoordGames.count_le_cube
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:09.230073+00:00
-- url     : https://prove2.me/theorems/1c6059a2-a5fa-4b2d-b21a-23efee71f94c
-- title:
--   §5, proof of Theorem 15, p.20 — the progress measure takes at most $1+m(m+1)(m+5)/6\le m^3$ values
-- statement:
--   For every integer $m\ge2$,
--   $$
--   \begin{aligned}
--   1+\sum_{g=0}^{m-1}\sum_{p=g+1}^{m}(p-g)+\sum_{g=0}^{m-1}(m-g)
--   &=1+\sum_{g=0}^{m-1}\frac{(m-g)(1+m-g)}{2}+\frac{m(1+m)}{2}\\
--   &=1+\sum_{x=1}^{m}\frac{x(1+x)}{2}+\frac{m(1+m)}{2}\\
--   &=1+\frac{m(m+1)(m+2)}{6}+\frac{m(1+m)}{2}\\
--   &=1+\frac{m(m+1)(m+5)}{6}\le m^3 .
--   \end{aligned}
--   $$
--
--   The left-hand side counts the possible values of the progress measure $\mu$: one value at Nash equilibria, and the quadruples allowed by $\mathrm{guard}+1\le\mathrm{NBR}\le|\mathrm{prefix}|\le m$ in its two other cases. With at most $3v$ steps per round this gives the bound $3vm^3$ of Theorem 15.
--
--   **Formalization Note** The identity is stated in natural numbers. Every subtraction is of a smaller number and every division is exact.
--
--   Differences from the source:
--   - encoding: rational expressions → natural-number arithmetic with truncated subtraction and division; reason: all subtractions are $p-g$ with $g<p$ or $m-g$ with $g<m$, and all quotients are exact, so the values coincide
-- source:
--   Apt–Simon–Wojtczak, Coordination Games on Weighted Directed Graphs, arXiv:1910.02693v2 (preprint), §5, proof of Theorem 15, counting display, p.20

import Mathlib

namespace WeightedCoordGames

/-- **The counting display** (Apt–Simon–Wojtczak, arXiv:1910.02693v2, §5, proof of Theorem 15,
p.20): for `m ≥ 2`,
`1 + Σ_{g=0}^{m−1} Σ_{p=g+1}^{m} (p − g) + Σ_{g=0}^{m−1} (m − g)`
`= 1 + Σ_{g=0}^{m−1} (m − g)(1 + m − g)/2 + m(1 + m)/2`
`= 1 + Σ_{x=1}^{m} x(1 + x)/2 + m(1 + m)/2`
`= 1 + m(m + 1)(m + 2)/6 + m(1 + m)/2`
`= 1 + m(m + 1)(m + 5)/6 ≤ m³`.

**Formalization Note.** Natural-number arithmetic; every subtraction has `g < m`, `g < p`, and
every division is exact (a product of two consecutive naturals is even, of three is divisible
by `6`, and `m(m+1)(m+5) = m(m+1)(m+2) + 3m(m+1)`). -/
theorem count_le_cube (m : ℕ) (hm : 2 ≤ m) :
    1 + (∑ g ∈ Finset.range m, ∑ p ∈ Finset.Icc (g + 1) m, (p - g)) +
          (∑ g ∈ Finset.range m, (m - g)) =
        1 + (∑ g ∈ Finset.range m, (m - g) * (1 + m - g) / 2) + m * (1 + m) / 2 ∧
    1 + (∑ g ∈ Finset.range m, (m - g) * (1 + m - g) / 2) + m * (1 + m) / 2 =
        1 + (∑ x ∈ Finset.Icc 1 m, x * (1 + x) / 2) + m * (1 + m) / 2 ∧
    1 + (∑ x ∈ Finset.Icc 1 m, x * (1 + x) / 2) + m * (1 + m) / 2 =
        1 + m * (m + 1) * (m + 2) / 6 + m * (1 + m) / 2 ∧
    1 + m * (m + 1) * (m + 2) / 6 + m * (1 + m) / 2 = 1 + m * (m + 1) * (m + 5) / 6 ∧
    1 + m * (m + 1) * (m + 5) / 6 ≤ m ^ 3 := by sorry

end WeightedCoordGames
