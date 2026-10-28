-- Prove2me | Theorems.Thm_StrategyproofMinimax_Circle_line_center_split
-- name    : StrategyproofMinimax.Circle.line_center_split
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T20:54:53.882538+00:00
-- url     : https://prove2.me/theorems/c1578d03-6712-410c-977e-6fb7492c73ae
-- title:
--   Lemma A.3 — splitting [0, 1] at y and choosing each centre with its length's probability
-- statement:
--   On the real line, with $d(a,b)=|a-b|$ and $\operatorname{cen}(a,b)=(a+b)/2$: for all $x,y\in[0,1]$,
--   $$d\big(x,\tfrac12\big)\le y\cdot d\big(x,\operatorname{cen}(0,y)\big)+(1-y)\cdot d\big(x,\operatorname{cen}(y,1)\big).$$
--   In words: cutting $[0,1]$ at $y$ and returning the centre of each piece with probability equal to its length can only raise the expected distance from any point $x$, compared with returning the centre $1/2$ of the whole interval. The paper applies this to arcs of the circle of length at most $1/2$, which behave as intervals.
--
--   **Formalization Note.** Stated on $\mathbb{R}$ with absolute values, exactly as on the page; `cen(0, y)` is written `(0 + y) / 2`.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 520, Lemma A.3

import Mathlib

namespace StrategyproofMinimax.Circle

/-- Lemma A.3 (p. 520), on the real line with `d(a, b) = |a - b|` and `cen(a, b) = (a + b)/2`:
for `x, y ∈ [0, 1]`, `d(x, 1/2) ≤ y · d(x, cen(0, y)) + (1 - y) · d(x, cen(y, 1))`. -/
theorem line_center_split (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |x - 1 / 2| ≤ y * |x - (0 + y) / 2| + (1 - y) * |x - (y + 1) / 2| := by sorry

end StrategyproofMinimax.Circle
