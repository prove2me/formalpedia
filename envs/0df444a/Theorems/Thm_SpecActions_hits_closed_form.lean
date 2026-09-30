-- Prove2me | Theorems.Thm_SpecActions_hits_closed_form
-- name    : SpecActions.hits_closed_form
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-10T18:42:17.673647+00:00
-- url     : https://prove2.me/theorems/8d7323d3-e50a-4ead-9866-2111b0c9eb2a
-- title:
--   Closed form for the expected hit count $S_n$
-- statement:
--   Let $S_n$ be the expected number of speculation hits by round $n$. Because a correct guess leaves the next call already cached, that round opens no speculation window, which gives the two-term recursion
--
--   $$S_0=0,\qquad S_1=p,\qquad S_n=p\,(1+S_{n-2})+(1-p)\,S_{n-1}.$$
--
--   For every $p\ge 0$ and every $n$,
--
--   $$S_n=\frac{p}{1+p}\,n+\frac{p^2}{(1+p)^2}\bigl(1-(-p)^n\bigr).$$
--
--   The characteristic polynomial $r^2-(1-p)r-p$ has roots $1$ and $-p$; since $r=1$ is a root, a constant particular solution collides with the homogeneous family and the particular solution is linear in $n$.
-- source:
--   Ye, Ahuja, Liargkovas, Lu, Kaffes, Peng, "Speculative Actions: A Lossless Framework for Faster Agentic Systems", ICLR 2026, arXiv:2510.04371, https://arxiv.org/abs/2510.04371, Appendix A (pp. 13–14), the recursion $S_n=p(k)(1+S_{n-2})+(1-p(k))S_{n-1}$ and its closed-form solution

import Definitions.Def_SpecActions_model

import Definitions.Def_SpecActions_model

namespace SpecActions
theorem hits_closed_form (p : ℝ) (hp : 0 ≤ p) (n : ℕ) :
    hits p n = p / (1 + p) * n + p ^ 2 / (1 + p) ^ 2 * (1 - (-p) ^ n) := by sorry
end SpecActions
