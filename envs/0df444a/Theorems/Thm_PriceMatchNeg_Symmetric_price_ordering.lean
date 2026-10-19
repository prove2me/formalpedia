-- Prove2me | Theorems.Thm_PriceMatchNeg_Symmetric_price_ordering
-- name    : PriceMatchNeg.Symmetric.price_ordering
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:58.056207+00:00
-- url     : https://prove2.me/theorems/b7b8431b-06b7-4b76-8197-a524a409d38c
-- title:
--   §3.2.2, p. 10 — with symmetric power, $0 < w^{SN} < w^{PM} \le a/2$
-- statement:
--   Let $a > 0$, $\gamma \in [0,1)$ and $\theta \in (0,1)$. With symmetric bargaining power ($\theta_i = \theta_j = \theta$),
--
--   $$0 < w^{SN} < w^{PM} \le \frac a2,$$
--
--   where $w^{SN}$ and $w^{PM} = w^{PM}_i$ are the closed forms of the SN and PM equilibrium wholesale prices.
--
--   Price matching thus leads to a strictly higher wholesale price than simultaneous negotiation.
--
--   **Formalization Note** The paper states $w^{PM} \ge w^{SN}$ with equality exactly at $\theta = 0$ or $1$; on $\theta \in (0,1)$ this is the strict inequality. The bounds $0 < w^{SN}$ and $w^{PM} \le a/2$ are added: the proof of Theorem 1 uses that both prices lie in $[0, a/2]$ without stating it.
-- source:
--   Shang & Cai, Implications of Price Matching in Supply Chain Negotiation, accepted manuscript (MSOM, forthcoming; SSRN 3021563), p. 10 (PDF 10), §3.2.2; proof of Theorem 1, Online Supplement p. 1 (PDF 34)

import Mathlib
import Definitions.Def_PriceMatchNeg_Symmetric_Model

namespace PriceMatchNeg.Symmetric

theorem price_ordering (P : Params) (hS : P.Standing) (θ : ℝ) (hθ : ValidPower θ) :
    0 < wSN P θ ∧ wSN P θ < wPM P θ θ ∧ wPM P θ θ ≤ P.a / 2 := by sorry

end PriceMatchNeg.Symmetric
