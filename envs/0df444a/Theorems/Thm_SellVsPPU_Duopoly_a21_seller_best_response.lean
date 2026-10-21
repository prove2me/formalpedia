-- Prove2me | Theorems.Thm_SellVsPPU_Duopoly_a21_seller_best_response
-- name    : SellVsPPU.Duopoly.a21_seller_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:13.277622+00:00
-- url     : https://prove2.me/theorems/ecc51ba3-2fbc-4237-8b2a-cebdfb6870e7
-- title:
--   A.2.1, p. 36 — seller best response, globally (stronger than printed)
-- statement:
--   Let $a>0$ be value per use, $q_m>0$ the maximum usage, $c>0$ the product cost, and $\delta\ge0$ the delivery cost per use. Assume the service cost $c_u=c/q_m+\delta$ does not exceed $a$.
--
--   Fix a service price $0<p_u\le a$ for which $c\le q_m p_u$. Among all real seller prices, $p_s=(c+q_m p_u)/2$ maximizes the seller's profit:
--
--   $$
--   \Pi_s(p_s',p_u)\le\Pi_s\!\left(\frac{c+q_mp_u}{2},p_u\right)
--   \quad\text{for every }p_s'\in\mathbb R.
--   $$
--
--   This is the global best-response claim underlying the equilibrium table.
--
--   **Formalization Note** The paper obtains the price from a first-order condition in the interior formula. The theorem additionally checks every seller price, including prices outside that formula's domain.
-- source:
--   Ladas, Kavadias & Loch, Product Selling vs. Pay-Per-Use Service, SSRN 3356458 manuscript (PDF of 16 Apr 2021; Management Science, doi:10.1287/mnsc.2021.4125), p. 36, A.2.1, seller best-response sentence

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model

namespace SellVsPPU.Duopoly

/-- Stronger than printed: the paper derives this price from a first-order condition; this theorem asserts global optimality over every real seller price. -/
theorem a21_seller_best_response (P : Params) (hP : P.Admissible)
    (pu : ℝ) (hpu : 0 < pu) (hpuA : pu ≤ P.a) (hc : P.c ≤ P.qm * pu) :
    ∀ ps' : ℝ, profitS P ps' pu ≤ profitS P ((P.c + P.qm * pu) / 2) pu := by sorry

end SellVsPPU.Duopoly
