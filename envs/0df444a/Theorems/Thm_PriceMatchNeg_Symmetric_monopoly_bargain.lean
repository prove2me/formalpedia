-- Prove2me | Theorems.Thm_PriceMatchNeg_Symmetric_monopoly_bargain
-- name    : PriceMatchNeg.Symmetric.monopoly_bargain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:05.25215+00:00
-- url     : https://prove2.me/theorems/8f867c26-4877-4bd6-ad61-df15c0891057
-- title:
--   §3.2.2, p. 10 — the single-channel Nash bargain is $\hat w_j = (1-\theta_j)a/2$ and the seller earns $(1-\theta_j^2)a^2/8$
-- statement:
--   Let $a > 0$, $\gamma \in [0,1)$ and let Buyer $j$ have bargaining power $\theta_j \in (0,1)$. Consider the bargain between the seller and Buyer $j$ alone over the wholesale price $w \ge 0$, with payoffs $\pi^M_j(w)$, $\pi^M_s(w)$ and disagreement point $(0,0)$.
--
--   1. A price is the Nash bargaining solution of this bargain if and only if it equals
--   $$\hat w_j = \frac{(1-\theta_j)a}{2}.$$
--   2. At that price the seller earns $\pi^M_s(\hat w_j) = \dfrac{(1-\theta_j^2)a^2}{8}$.
--
--   This is the seller's disagreement payoff in the first price-matching negotiation.
-- source:
--   Shang & Cai, Implications of Price Matching in Supply Chain Negotiation, accepted manuscript (MSOM, forthcoming; SSRN 3021563), p. 10 (PDF 10), §3.2.2

import Mathlib
import Definitions.Def_PriceMatchNeg_Symmetric_Model

namespace PriceMatchNeg.Symmetric

theorem monopoly_bargain (P : Params) (hS : P.Standing) (θj : ℝ) (hθ : ValidPower θj) :
    (∀ w, IsMonoBargain P θj w ↔ w = (1 - θj) * P.a / 2) ∧
    piMs P ((1 - θj) * P.a / 2) = (1 - θj ^ 2) * P.a ^ 2 / 8 := by sorry

end PriceMatchNeg.Symmetric
