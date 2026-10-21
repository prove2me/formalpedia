-- Prove2me | Theorems.Thm_PriceMatchNeg_Symmetric_diagonal_profits
-- name    : PriceMatchNeg.Symmetric.diagonal_profits
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:04.708578+00:00
-- url     : https://prove2.me/theorems/dca37c56-03c0-4f47-991b-63a0f78f96fc
-- title:
--   Proof of Theorem 1, Online Supplement p. 1 — at equal prices, the seller's profit rises on $[0, a/2]$ and each buyer's falls on $[0, a]$
-- statement:
--   Let $a > 0$ and $\gamma \in [0,1)$. When both buyers pay the same wholesale price $w$, the second-stage profits are
--
--   $$\pi_s(w,w) = \frac{2w(a-w)}{(1+\gamma)(2-\gamma)}, \qquad \pi_i(w,w) = \frac{(1-\gamma)(a-w)^2}{(1+\gamma)(2-\gamma)^2}.$$
--
--   Moreover $w \mapsto \pi_s(w,w)$ is strictly increasing on $[0, a/2]$, and $w \mapsto \pi_i(w,w)$ is strictly decreasing on $[0, a]$.
--
--   The seller therefore prefers a higher common wholesale price and the buyers a lower one, which turns the price ordering of the previous milestone into the profit comparison of Theorem 1.
--
--   **Formalization Note** The paper prints the buyer's profit as $(a-w)/((1+\gamma)(2-\gamma))$, which is the sales quantity $\hat x_i(w,w)$, not the profit; the formal statement uses the profit $\pi_i(w,w) = (1-\gamma^2)\hat x_i(w,w)^2$. Both are decreasing on $[0,a]$.
-- source:
--   Shang & Cai, Implications of Price Matching in Supply Chain Negotiation, accepted manuscript (MSOM, forthcoming; SSRN 3021563), proof of Theorem 1, Online Supplement p. 1 (PDF 34)

import Mathlib
import Definitions.Def_PriceMatchNeg_Symmetric_Model

namespace PriceMatchNeg.Symmetric

theorem diagonal_profits (P : Params) (hS : P.Standing) :
    (∀ w, piS P w w = 2 * w * (P.a - w) / ((1 + P.γ) * (2 - P.γ))) ∧
    StrictMonoOn (fun w => piS P w w) (Set.Icc 0 (P.a / 2)) ∧
    (∀ w, piB P w w = (1 - P.γ) * (P.a - w) ^ 2 / ((1 + P.γ) * (2 - P.γ) ^ 2)) ∧
    StrictAntiOn (fun w => piB P w w) (Set.Icc 0 P.a) := by sorry

end PriceMatchNeg.Symmetric
