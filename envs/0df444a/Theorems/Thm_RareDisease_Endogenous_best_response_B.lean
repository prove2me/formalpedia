-- Prove2me | Theorems.Thm_RareDisease_Endogenous_best_response_B
-- name    : RareDisease.Endogenous.best_response_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:07:05.668637+00:00
-- url     : https://prove2.me/theorems/078aed17-3d94-4161-8e9a-50dd666c6fa4
-- title:
--   Equations (14)–(15) — unique outcome-based best response
-- statement:
--   Let $k>0$ and $\alpha,\beta\in[0,1)$. In Setting (1B), where the manufacturer chooses price $p$ and target efficacy $e$ but is paid only when treatment succeeds, its complete best-response set is
--   $$
--   \operatorname{BR}_B(k,\alpha,\beta)=\left\{\left(\frac{1}{2(1-\beta)},\frac{1}{8(1-\alpha)k(1-\beta)}\right)\right\}.
--   $$
--   The price differs from Setting (1A), while target efficacy is the same at a fixed policy.
--
--   **Formalization Note** The text preceding (14) cites equation (9), which describes consortium pricing; the manufacturer-pricing objective here is equation (8). The manufacturer chooses $p\ge0$ and $e>0$, without an upper bound on $e$.
-- source:
--   Olsder, Martagan, Tang, Improving Access to Rare Disease Treatments: Optimal Subsidies, Pricing, and Payment, SSRN working paper 3481150 (version of 2019-11-13), p. 13, §4.2, equations (14)–(15)

import Mathlib
import Definitions.Def_RareDisease_Endogenous_Setting

namespace RareDisease.Endogenous

/-- Equations (14)–(15), p. 13: the joint outcome-based best response is unique. -/
theorem best_response_B (k α β : ℝ) (hk : 0 < k) (hpolicy : IsPolicy α β) :
    BRB k α β = {
      (1 / (2 * (1 - β)),
       1 / (8 * (1 - α) * k * (1 - β)))} := by sorry

end RareDisease.Endogenous
