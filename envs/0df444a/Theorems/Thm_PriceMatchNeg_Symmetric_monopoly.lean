-- Prove2me | Theorems.Thm_PriceMatchNeg_Symmetric_monopoly
-- name    : PriceMatchNeg.Symmetric.monopoly
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:46.791956+00:00
-- url     : https://prove2.me/theorems/301ab8c3-0096-47e4-ac6a-94234986a5b0
-- title:
--   §3.1.2, p. 9 — single-channel monopoly: $p^M_j = (a+w_j)/2$, $\pi^M_j = (a-w_j)^2/4$, $\pi^M_s = w_j(a-w_j)/2$
-- statement:
--   Let $a > 0$, $\gamma \in [0,1)$ and $w_j \in \mathbb R$. When only Buyer $j$ trades, its demand is $a - p_j$ and its profit is $(p_j - w_j)(a - p_j)$.
--
--   1. The price $p_j$ maximizes this profit if and only if $p_j = p^M_j = (a + w_j)/2$.
--   2. Buyer $j$'s and the seller's monopoly profits are
--   $$\pi^M_j(w_j) = \frac{(a-w_j)^2}{4}, \qquad \pi^M_s(w_j) = \frac{w_j(a-w_j)}{2}.$$
--
--   The seller's monopoly profit is its disagreement payoff in every negotiation of the model.
-- source:
--   Shang & Cai, Implications of Price Matching in Supply Chain Negotiation, accepted manuscript (MSOM, forthcoming; SSRN 3021563), p. 9 (PDF 9), §3.1.2

import Mathlib
import Definitions.Def_PriceMatchNeg_Symmetric_Model

namespace PriceMatchNeg.Symmetric

theorem monopoly (P : Params) (hS : P.Standing) (w : ℝ) :
    (∀ p, (∀ q, monoProfit P w q ≤ monoProfit P w p) ↔ p = pMono P w) ∧
    piMb P w = (P.a - w) ^ 2 / 4 ∧
    piMs P w = w * (P.a - w) / 2 := by sorry

end PriceMatchNeg.Symmetric
