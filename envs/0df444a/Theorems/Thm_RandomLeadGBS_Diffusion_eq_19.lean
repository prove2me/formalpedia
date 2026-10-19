-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_eq_19
-- name    : RandomLeadGBS.Diffusion.eq_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:17.868986+00:00
-- url     : https://prove2.me/theorems/c0089e89-4f46-45d3-95b0-8b7cf510f972
-- title:
--   (19), p. 17 — conservation law βE Ẑ^r(∞) = r for the artificial chain
-- statement:
--   Under the standing assumptions, with centering $x_*\equiv 0$, fix $r>0$ and let $p$ be any stationary distribution of the artificial birth–death chain $\hat Y^r$, whose in-transit level is $\hat Z^r = \lceil\hat T^r\rceil$. Then $\mathbb E\hat Z^r(\infty)$ is finite and
--   $$
--   \beta\,\mathbb E\hat Z^r(\infty) = r .
--   $$
--   With (14) it gives $\mathbb E Z^r(\infty) = \mathbb E\hat Z^r(\infty)$, used to derive (31).
--
--   **Formalization Note** The expectation is $\sum_j p(j)\lceil\hat T(j)\rceil$, with its summability asserted. Centering $x_*\equiv 0$ (p. 12).
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, p. 17, (19)

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion

theorem eq_19 (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0) (r : ℝ) (hr : 0 < r)
    (p : ℤ → ℝ) (hp : IsArtStationary P r p) :
    Summable (fun j : ℤ => p j * (artZ P r j : ℝ)) ∧
    P.β * ∑' j : ℤ, p j * (artZ P r j : ℝ) = r := by sorry

end RandomLeadGBS.Diffusion
