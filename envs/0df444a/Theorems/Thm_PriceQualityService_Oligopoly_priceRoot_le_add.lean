-- Prove2me | Theorems.Thm_PriceQualityService_Oligopoly_priceRoot_le_add
-- name    : PriceQualityService.Oligopoly.priceRoot_le_add
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:18:04.05299+00:00
-- url     : https://prove2.me/theorems/5a056d11-9cd4-44e7-8247-b7e71ac19ff2
-- title:
--   $\varphi_i(A) \le A + k_i$ when the aggregate exceeds firm $i$'s attraction by at least one
-- statement:
--   Let $k$ and $w$ be real numbers and $A$ an aggregate with $A - \exp(w - \varphi(A)) \ge 1$, where $\varphi(A)$ is the price root for unit cost $k$ and price-free utility $w$. Then
--   $$
--   \varphi(A) \le A + k .
--   $$
--
--   At an equilibrium aggregate $A = 1 + \sum_j \exp(w_j - p_j)$ one has $A - \exp(w_i - p_i) = 1 + \sum_{j \ne i} \exp(w_j - p_j) \ge 1$, so the hypothesis holds there; the bound compares equilibrium prices with the monopoly markup.
--
--   **Formalization Note** The paper writes "$\varphi_i(A) \le A + c_i q_i^{*2} + t_i^*(a_i - b_i q_i^*)$ for any $i$", but its derivation uses $A - \exp(\cdot) \ge 1$, which fails for small $A$ (for $A < 1$, $\varphi(A) - k > 1 > A$). The hypothesis makes that condition explicit.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 3 (PDF p. 36), proof of Theorem 2

import Mathlib
import Definitions.Def_PriceQualityService_Oligopoly_PriceRoot

namespace PriceQualityService.Oligopoly

/-- Online Supplement p. 3: if the aggregate `A` exceeds the PriceQualityService.Joint.attraction
`exp(w − φ(A))` of the product by at least one (as at an equilibrium aggregate, where
`A − exp(w_i − p_i) = 1 + ∑_{j ≠ i} exp(w_j − p_j)`), then `φ(A) ≤ A + k`. -/
theorem priceRoot_le_add (k w A : ℝ) (h : 1 ≤ A - Real.exp (w - priceRoot k w A)) :
    priceRoot k w A ≤ A + k := by sorry

end PriceQualityService.Oligopoly
