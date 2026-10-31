-- Prove2me | Theorems.Thm_ParallelLotteries_gamma_eq_f
-- name    : ParallelLotteries.gamma_eq_f
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:59.94857+00:00
-- url     : https://prove2.me/theorems/65c62deb-60ba-4cff-9a6a-16261a384d94
-- title:
--   The two-item constant: $\gamma$ of (58) equals $f(p_i,p_j)$ of (59)
-- statement:
--   Let $k\ge1$ and $0<p_i<1/k<p_j\le1$, and let $y_i,y_j$ satisfy $y_i+y_j=1$ and $C(y)=\frac1k\bigl(\frac{y_i}{p_i}+\frac{y_j}{p_j}\bigr)=1$. Then
--   $$\frac{y_i}{1-(1-p_i)^k}+\frac{y_j}{1-(1-p_j)^k}=f(p_i,p_j)=\frac{p_j-1/k}{p_j-p_i}\,h(p_i)+\frac{1/k-p_i}{p_j-p_i}\,h(p_j),$$
--   where $h(p)=pk/(1-(1-p)^k)$ (60).
--
--   This turns the two-item bound $\gamma$ of (58) into the explicit function $f$ whose supremum is $2-1/k$.
--
--   Differences from the source:
--   - reading: "the choice of $y$ satisfying $y_i+y_j=1$ and $C(y)=1$" → hypotheses $y_i+y_j=1$ and $\frac1k(y_i/p_i+y_j/p_j)=1$, on the range $0<p_i<1/k<p_j\le1$; reason: $y$ is supported on $\{i,j\}$, so this is its cost (49); the range is (53) with $p_i>0$ (division in (49)) and $p_j\le1$ (a win probability)
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), App. D.2, (58)–(60), p.34

import Mathlib
import Definitions.Def_ParallelLotteries_hf

namespace ParallelLotteries

/-- **The two-item constant γ equals f(p_i, p_j): (58) = (59)** — Arnosti–Randolph, SSRN 3370605
(preprint), App. D.2, p.34: "γ = y_i/(1 − (1 − p_i)^k) + y_j/(1 − (1 − p_j)^k) (58). Solve for the
choice of y satisfying y_i + y_j = 1 and C(y) = 1, and substitute into (58). After simplification
we get the following expression for γ, which we write in terms of the functions f and h:
f(p_i, p_j) := (p_j − 1/k)/(p_j − p_i) h(p_i) + (1/k − p_i)/(p_j − p_i) h(p_j) = γ, (59) where
h(p) := pk/(1 − (1 − p)^k). (60)"

For `k ≥ 1`, `0 < p_i < 1/k < p_j ≤ 1`, and `y_i, y_j` with `y_i + y_j = 1` and
`C(y) = (1/k)(y_i/p_i + y_j/p_j) = 1`,
`y_i/(1 − (1 − p_i)^k) + y_j/(1 − (1 − p_j)^k) = f(p_i, p_j)`.

**Formalization Note.** `y` is supported on `{i, j}`, so its cost (49) is
`(1/k)(y_i/p_i + y_j/p_j)`. The range `1/k < p_j ≤ 1` is empty for `k = 1`, as on the page (the
two-item case (53) cannot occur for `k = 1`). -/
theorem gamma_eq_f (k : ℕ) (hk : 1 ≤ k) (pi pj yi yj : ℝ) (hpi : 0 < pi)
    (hpik : pi < 1 / (k : ℝ)) (hpjk : 1 / (k : ℝ) < pj) (hpj : pj ≤ 1) (hsum : yi + yj = 1)
    (hcost : 1 / (k : ℝ) * (yi / pi + yj / pj) = 1) :
    yi / (1 - (1 - pi) ^ k) + yj / (1 - (1 - pj) ^ k) = fval k pi pj := by sorry

end ParallelLotteries
