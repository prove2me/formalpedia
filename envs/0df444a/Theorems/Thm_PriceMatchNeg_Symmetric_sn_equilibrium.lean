-- Prove2me | Theorems.Thm_PriceMatchNeg_Symmetric_sn_equilibrium
-- name    : PriceMatchNeg.Symmetric.sn_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:55.154559+00:00
-- url     : https://prove2.me/theorems/aa03f488-bad0-41ad-b44f-4edde9e634d2
-- title:
--   §3.2.1, p. 9 — with symmetric power θ, the unique SN equilibrium is $w_1 = w_2 = w^{SN}$
-- statement:
--   Let $a > 0$, $\gamma \in [0,1)$ and let both buyers have bargaining power $\theta \in (0,1)$. A pair $(w_1, w_2)$ is an equilibrium of simultaneous negotiation (each $w_i \in [0,a]$ is the Nash bargaining solution of dyad $i$ given $w_j$, with payoffs $\pi_i(\cdot,w_j)$, $\pi_s(\cdot,w_j)$ and disagreement point $(0,\pi^M_s(w_j))$) if and only if
--
--   $$w_1 = w_2 = w^{SN} = \frac{(1-\theta)(1-\gamma)(2+\gamma)a}{2(1-\gamma)(2+\gamma) + \gamma^2(1+\gamma)(2-\gamma)\theta}.$$
--
--   The statement contains both existence and uniqueness of the SN equilibrium.
--
--   **Formalization Note** The paper asserts uniqueness ("the unique bargaining solution") without proof; the formal statement makes that assertion part of the target.
-- source:
--   Shang & Cai, Implications of Price Matching in Supply Chain Negotiation, accepted manuscript (MSOM, forthcoming; SSRN 3021563), p. 9 (PDF 9), §3.2.1; proof of Theorem 1, Online Supplement p. 1 (PDF 34)

import Mathlib
import Definitions.Def_PriceMatchNeg_Symmetric_Model

namespace PriceMatchNeg.Symmetric

theorem sn_equilibrium (P : Params) (hS : P.Standing) (θ : ℝ) (hθ : ValidPower θ) :
    ∀ w1 w2, IsSNEq P θ θ w1 w2 ↔ w1 = wSN P θ ∧ w2 = wSN P θ := by sorry

end PriceMatchNeg.Symmetric
