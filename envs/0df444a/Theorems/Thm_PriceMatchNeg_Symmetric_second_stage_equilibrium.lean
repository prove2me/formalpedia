-- Prove2me | Theorems.Thm_PriceMatchNeg_Symmetric_second_stage_equilibrium
-- name    : PriceMatchNeg.Symmetric.second_stage_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:49.872991+00:00
-- url     : https://prove2.me/theorems/50c38d1d-22c8-4e5e-b6df-775d38a7420e
-- title:
--   §3.1.1, pp. 8–9 — the retail Bertrand equilibrium is $(\hat p_i, \hat p_j)$, with sales $\hat x_i$ and profits (1)–(2)
-- statement:
--   Let $a > 0$ and $\gamma \in [0,1)$, and fix arbitrary wholesale prices $w_i, w_j \in \mathbb R$. In the retail game Buyer $i$ chooses $p_i$ to maximize $(p_i - w_i)\,x_i(p_i, p_j)$, where $x_i(p_i,p_j) = ((1-\gamma)a - p_i + \gamma p_j)/(1-\gamma^2)$.
--
--   1. A pair $(p_i, p_j)$ is a Bertrand equilibrium if and only if $p_i = \hat p_i(w_i,w_j)$ and $p_j = \hat p_j(w_j,w_i)$, where
--   $$\hat p_i(w_i,w_j) = \frac{(2-\gamma-\gamma^2)a + 2w_i + \gamma w_j}{4-\gamma^2}.$$
--   2. The resulting sales are $x_i(\hat p_i, \hat p_j) = \hat x_i(w_i,w_j) = \dfrac{(2-\gamma-\gamma^2)a - (2-\gamma^2)w_i + \gamma w_j}{(1-\gamma^2)(4-\gamma^2)}$.
--   3. The equilibrium profits are
--   $$\pi_i(w_i,w_j) = (1-\gamma^2)\,[\hat x_i(w_i,w_j)]^2, \qquad \pi_s(w_i,w_j) = w_i\,\hat x_i(w_i,w_j) + w_j\,\hat x_j(w_j,w_i).$$
--
--   These are equations (1)–(2) of the paper, the payoffs of every first-stage negotiation.
--
--   **Formalization Note** Retail prices range over all reals; $\pi_i$ and $\pi_s$ are defined as the primitive profits evaluated at $(\hat p_i,\hat p_j)$, so (1)–(2) are genuine identities to prove.
-- source:
--   Shang & Cai, Implications of Price Matching in Supply Chain Negotiation, accepted manuscript (MSOM, forthcoming; SSRN 3021563), p. 8 (PDF 8), §3.1.1 (p̂_i, x̂_i); p. 9 (PDF 9), equations (1), (2)

import Mathlib
import Definitions.Def_PriceMatchNeg_Symmetric_Model

namespace PriceMatchNeg.Symmetric

theorem second_stage_equilibrium (P : Params) (hS : P.Standing) (wi wj : ℝ) :
    (∀ pi pj, IsBertrandEq P wi wj pi pj ↔ pi = pHat P wi wj ∧ pj = pHat P wj wi) ∧
    demand P (pHat P wi wj) (pHat P wj wi) = xHat P wi wj ∧
    piB P wi wj = (1 - P.γ ^ 2) * xHat P wi wj ^ 2 ∧
    piS P wi wj = wi * xHat P wi wj + wj * xHat P wj wi := by sorry

end PriceMatchNeg.Symmetric
