-- Prove2me | Theorems.Thm_SubstitutePricing_Dynamic_eq_5
-- name    : SubstitutePricing.Dynamic.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:03.124648+00:00
-- url     : https://prove2.me/theorems/955d359d-e7cd-4483-8266-fad863627423
-- title:
--   (5) — Bellman objective as marginal revenue plus continuation value
-- statement:
--   For any continuation value $V$, inventory $x$, and finite price vector $r$, the one-period objective can be rearranged as
--
--   $$
--   \operatorname{obj}_V(x,r)=\xi_V(x,r)+V(x),\qquad \xi_V(x,r)=\lambda\sum_{i\in S(x)}P_i(x,r)\bigl[r_i-(V(x)-V(x-e^i))\bigr].
--   $$
--
--   This identity is the pointwise algebra behind equation (5), and connects the Bellman objective to the marginal revenue optimized in Theorem 1. The model assumes $\mu>0$ and $0<\lambda\leq1$.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 323, (5)

import Definitions.Def_SubstitutePricing_Dynamic_Model

namespace SubstitutePricing.Dynamic
/-- Pointwise rearrangement behind (5). -/
theorem eq_5 (M : Model) (hM : M.Assumptions)
    (V : (Fin M.n → ℕ) → ℝ) (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) :
    M.obj V x r = M.xi V x r + V x := by sorry
end SubstitutePricing.Dynamic
