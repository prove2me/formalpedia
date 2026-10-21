-- Prove2me | Theorems.Thm_TradingFavors_Existence_lemma_A_3
-- name    : TradingFavors.Existence.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:28.775584+00:00
-- url     : https://prove2.me/theorems/826a4495-b5cb-4f7d-94a7-fd3b363268d9
-- title:
--   Lemma A.3, p. A5 (PDF 35) — first-passage discounts Γ(0,1,k,k) > Γ(1,0,k+1,k) > Γ(1,1,k+1,k) under σᴸ
-- statement:
--   Assume the standing assumptions and let the firms play $\sigma^L$. For a state $(x_1,x_2,k')$ let $\Gamma(x_1,x_2,k',k)=E[e^{-\gamma\tau}]$, where $\tau$ is the first-passage time of the chain from $(x_1,x_2,k')$ to $(1,0,k)$. Then for every $k\in\{0,1,\dots,L-1\}$
--   $$
--   \Gamma(0,1,k,k)>\Gamma(1,0,k+1,k)>\Gamma(1,1,k+1,k).
--   $$
--
--   This comparison of discounted hitting times is the ingredient that makes condition (14) sufficient in Lemma 4.
--
--   **Formalization Note** $\Gamma$ is computed on the uniformized chain killed at the target: $\Gamma=\sum_n(\Lambda/(\Lambda+\gamma))^n\,\mathbb P(\text{first hit at jump }n)$, which equals $E[e^{-\gamma\tau}]$ for the continuous-time chain. In Lean the target comes first: `Gam θ σ (1,0,k) (x₁,x₂,k')`. For $L=0$ the range of $k$ is empty.
-- source:
--   Hu & Caldentey, Trust and Reciprocity in Firms’ Capacity Sharing, SSRN 4348127 (version of February 6, 2023), p. A5 (PDF 35), Lemma A.3

import Mathlib
import Definitions.Def_TradingFavors_Existence_Model

namespace TradingFavors.Existence

theorem lemma_A_3 (θ : Params) (hθ : θ.Standing) (L : ℕ) (k : ℤ)
    (hk0 : 0 ≤ k) (hkL : k ≤ (L : ℤ) - 1) :
    Gam θ (sigmaL L) (1, 0, k) (1, 0, k + 1) < Gam θ (sigmaL L) (1, 0, k) (0, 1, k) ∧
    Gam θ (sigmaL L) (1, 0, k) (1, 1, k + 1) < Gam θ (sigmaL L) (1, 0, k) (1, 0, k + 1) := by sorry

end TradingFavors.Existence
