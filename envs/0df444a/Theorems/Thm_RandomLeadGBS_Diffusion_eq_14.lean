-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_eq_14
-- name    : RandomLeadGBS.Diffusion.eq_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:02.73685+00:00
-- url     : https://prove2.me/theorems/1442b903-2936-4137-ae5d-ef41afa8aea9
-- title:
--   (14), p. 13 — conservation law βE Z^r(∞) = r for the GBS chain
-- statement:
--   Under the standing assumptions, with centering $x_*\equiv 0$, fix $r>0$ and let $p$ be any stationary distribution of the GBS chain $(Y^r,Z^r)$. Then the mean number of items in transit is finite and
--   $$
--   \beta\,\mathbb E Z^r(\infty) = r .
--   $$
--   In steady state the average rate of item arrivals equals the customer arrival rate. Together with its analogue (19) for the artificial chain, it identifies $\mathbb E Z^r(\infty) = \mathbb E\hat Z^r(\infty)$, which turns the target gap $\mathbb E\lceil\hat T^r\rceil - \mathbb E\lceil T^r\rceil$ into the gap $\mathbb E D^r(\infty)$.
--
--   **Formalization Note** The expectation is the series $\sum_s p(s)\,z(s)$; its summability is part of the conclusion, so the identity cannot hold through a divergent series evaluating to $0$. The centering $x_*\equiv 0$ is the paper's "without loss of generality" convention of §4 (p. 12).
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, p. 13, (14)

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion

theorem eq_14 (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0) (r : ℝ) (hr : 0 < r)
    (p : State → ℝ) (hp : IsStationary P r p) :
    Summable (fun s : State => p s * (s.2 : ℝ)) ∧
    P.β * ∑' s : State, p s * (s.2 : ℝ) = r := by sorry

end RandomLeadGBS.Diffusion
