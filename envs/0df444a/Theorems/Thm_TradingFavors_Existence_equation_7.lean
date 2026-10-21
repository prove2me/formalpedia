-- Prove2me | Theorems.Thm_TradingFavors_Existence_equation_7
-- name    : TradingFavors.Existence.equation_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:10.854541+00:00
-- url     : https://prove2.me/theorems/325e0285-ad30-4d63-9d44-28494d5dec69
-- title:
--   Equation (7), p. 12 (PDF 12) — payoffs in a cluster where neither firm collaborates are πᴺᶜᵢ(0), πᴺᶜᵢ(1)
-- statement:
--   Fix parameters satisfying the standing assumptions, a strategy profile $\sigma$ and a balance $k$ with $\sigma_1(k)=\sigma_2(k)=1$ (neither firm accepts transfers at $k$). Then for $i=1,2$
--   $$
--   \pi_i(0,0,k\mid\sigma)=\pi_i(0,1,k\mid\sigma)=\pi_i^{NC}(0),\qquad \pi_i(1,0,k\mid\sigma)=\pi_i(1,1,k\mid\sigma)=\pi_i^{NC}(1),
--   $$
--   where
--   $$
--   \pi_i^{NC}(0)=\frac{(\mu_i+\gamma)\lambda_i(p_i-l_i)}{(\lambda_i+\mu_i+\gamma)\gamma},\qquad \pi_i^{NC}(1)=\frac{\lambda_i\mu_i(p_i-l_i)}{(\lambda_i+\mu_i+\gamma)\gamma}.
--   $$
--
--   These are firm $i$'s discounted payoffs when idle and when busy under no collaboration; they are the boundary values from which every recursion of the paper starts.
--
--   **Formalization Note** Payoffs are written in each firm's own coordinates (`pi2 θ σ x2 x1 k`).
-- source:
--   Hu & Caldentey, Trust and Reciprocity in Firms’ Capacity Sharing, SSRN 4348127 (version of February 6, 2023), p. 12 (PDF 12), eq. (7); proof p. A1 (PDF 31)

import Mathlib
import Definitions.Def_TradingFavors_Existence_Model

namespace TradingFavors.Existence

theorem equation_7 (θ : Params) (hθ : θ.Standing) (σ : Profile) (k : ℤ)
    (h1 : σ.s1 k = 1) (h2 : σ.s2 k = 1) :
    pi1 θ σ 0 0 k = piNC1 θ 0 ∧ pi1 θ σ 0 1 k = piNC1 θ 0 ∧
    pi1 θ σ 1 0 k = piNC1 θ 1 ∧ pi1 θ σ 1 1 k = piNC1 θ 1 ∧
    pi2 θ σ 0 0 k = piNC2 θ 0 ∧ pi2 θ σ 0 1 k = piNC2 θ 0 ∧
    pi2 θ σ 1 0 k = piNC2 θ 1 ∧ pi2 θ σ 1 1 k = piNC2 θ 1 := by sorry

end TradingFavors.Existence
