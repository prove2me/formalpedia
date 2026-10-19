-- Prove2me | Theorems.Thm_PriceMatchNeg_Symmetric_pm_equilibrium
-- name    : PriceMatchNeg.Symmetric.pm_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:58.094298+00:00
-- url     : https://prove2.me/theorems/64db9467-8d38-4fca-a684-22ece0a48a7a
-- title:
--   §3.2.2, p. 10 — the unique PM equilibrium wholesale price is $w^{PM}_i$
-- statement:
--   Let $a > 0$, $\gamma \in [0,1)$, and let the first buyer $i$ and the other buyer $j$ have bargaining powers $\theta_i, \theta_j \in (0,1)$. Under price matching, a price $w$ is an equilibrium wholesale price ($w \in [0,a]$ is the Nash bargaining solution of the seller and Buyer $i$ with payoffs $\pi_i(w,w)$, $\pi_s(w,w)$ and disagreement point $(0, \pi^M_s(\hat w_j))$, $\hat w_j$ the single-channel bargain with Buyer $j$) if and only if
--
--   $$w = w^{PM}_i = \frac{\Bigl(3 - \theta_i - \sqrt{1 - \gamma\theta_i + \gamma^2\theta_i + \theta_i^2 + (1+\gamma)(2-\gamma)\theta_i\theta_j^2}\Bigr)a}{4}.$$
--
--   The statement contains both existence and uniqueness of the PM equilibrium price.
-- source:
--   Shang & Cai, Implications of Price Matching in Supply Chain Negotiation, accepted manuscript (MSOM, forthcoming; SSRN 3021563), p. 10 (PDF 10), §3.2.2; proof of Theorem 1, Online Supplement p. 1 (PDF 34)

import Mathlib
import Definitions.Def_PriceMatchNeg_Symmetric_Model

namespace PriceMatchNeg.Symmetric

theorem pm_equilibrium (P : Params) (hS : P.Standing) (θi θj : ℝ)
    (hθi : ValidPower θi) (hθj : ValidPower θj) :
    ∀ w, IsPMPrice P θi θj w ↔ w = wPM P θi θj := by sorry

end PriceMatchNeg.Symmetric
