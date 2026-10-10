-- Prove2me | Theorems.Thm_PriceQualityService_Surplus_consumer_surplus_at_optimum
-- name    : PriceQualityService.Surplus.consumer_surplus_at_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:18:08.023926+00:00
-- url     : https://prove2.me/theorems/37dc35d1-cc64-44d8-a1ed-a3c6d8742b55
-- title:
--   Consumer surplus at an equal-markup optimum is $\log(1+r)$
-- statement:
--   Let $\mathbf p,\mathbf q,\mathbf t\in\mathbb R^N$ and $r\in\mathbb R$. Suppose every product carries the markup $1+r$,
--   $$
--   p_i-c_iq_i^2-t_i(a_i-b_iq_i)=1+r\quad\text{for all } i\in\mathcal N,
--   $$
--   and the profit equals $r$, $\Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)=r$. Then
--   $$
--   \sum_{i\in\mathcal N}\exp(\alpha_iq_i-p_i+t_is_i)=r\qquad\text{and}\qquad \mathrm{CS}(\mathbf p,\mathbf q,\mathbf t)=\log(1+r).
--   $$
--
--   This is the chain of equalities in the proof of Proposition 5 that expresses the consumer surplus at each of the three optima through the optimal profit, so that the ordering of profits becomes an ordering of consumer surplus.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement pp. 1–2 (PDF pp. 34–35), proof of Proposition 5

import Mathlib
import Definitions.Def_PriceQualityService_Surplus_Profit
import Definitions.Def_PriceQualityService_Surplus_ConsumerSurplus

namespace PriceQualityService.Surplus

open Finset

/-- Consumer surplus at an equal-markup optimum, Wang, Ke & Cui, accepted manuscript
(SSRN 3766191), Online Supplement pp. 1–2, proof of Proposition 5 (the chain of equalities
ending in `log(1 + r†)`). If every product's markup `p_i − c_i q_i² − t_i(a_i − b_i q_i)` equals
`1 + r` and the profit `Π(p, q, t; 𝒩)` equals `r`, then the total attraction
`∑_i exp(α_i q_i − p_i + t_i s_i)` equals `r` and consumer surplus equals `log(1 + r)`. -/
theorem consumer_surplus_at_optimum {N : ℕ} (α a b c s : Fin N → ℝ) (p q t : Fin N → ℝ)
    (r : ℝ) (hm : ∀ i, p i - c i * q i ^ 2 - t i * (a i - b i * q i) = 1 + r)
    (hprofit : PriceQualityService.Joint.profit α a b c s p q t = r) :
    ∑ i, PriceQualityService.Joint.attraction α s p q t i = r ∧ consumerSurplus α s p q t = Real.log (1 + r) := by sorry

end PriceQualityService.Surplus
