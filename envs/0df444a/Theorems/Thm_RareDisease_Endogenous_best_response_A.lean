-- Prove2me | Theorems.Thm_RareDisease_Endogenous_best_response_A
-- name    : RareDisease.Endogenous.best_response_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:07:07.469882+00:00
-- url     : https://prove2.me/theorems/dfa7552e-890c-4169-a8e1-bff19b9a295f
-- title:
--   Equations (11)–(12) — unique sales-based best response
-- statement:
--   Let $k>0$ be the R&D cost scale and let $\alpha,\beta\in[0,1)$ be a subsidy policy. In Setting (1A), where the manufacturer chooses price $p$ and target efficacy $e$ and is paid per sale, its complete best-response set is
--   $$
--   \operatorname{BR}_A(k,\alpha,\beta)=\left\{\left(\frac{1}{16(1-\alpha)k(1-\beta)^2},\frac{1}{8(1-\alpha)k(1-\beta)}\right)\right\}.
--   $$
--   Thus equations (11) and (12) give the unique joint price and efficacy choice, rather than merely one stationary point.
--
--   **Formalization Note** Manufacturer choices range over $p\ge0$ and $e>0$, as in the game definition; the paper does not impose $e\le1$.
-- source:
--   Olsder, Martagan, Tang, Improving Access to Rare Disease Treatments: Optimal Subsidies, Pricing, and Payment, SSRN working paper 3481150 (version of 2019-11-13), p. 12, §4.1, equations (11)–(12)

import Mathlib
import Definitions.Def_RareDisease_Endogenous_Setting

namespace RareDisease.Endogenous

/-- Equations (11)–(12), p. 12: the joint sales-based best response is unique. -/
theorem best_response_A (k α β : ℝ) (hk : 0 < k) (hpolicy : IsPolicy α β) :
    BRA k α β = {
      (1 / (16 * (1 - α) * k * (1 - β) ^ 2),
       1 / (8 * (1 - α) * k * (1 - β)))} := by sorry

end RareDisease.Endogenous
