-- Prove2me | Theorems.Thm_UnfairML_Coverage_eq_52
-- name    : UnfairML.Coverage.eq_52
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:28.321516+00:00
-- url     : https://prove2.me/theorems/14fb2ee1-9899-406a-80dd-680105135ed1
-- title:
--   Eqs. (48), (52), p. 44 — closed form of the protected coverage rate at the EO-optimal effort
-- statement:
--   Work in the model of §3 under the standing assumptions and case (1), with $\tau(s)=ks/(1-\gamma_r s)$ and $k$ in the range of p. 23. Let $s$ be any maximizer of $\pi_{EO}$ on $[0,1/(2\gamma_r)]$. Then
--   $$\frac{\gamma_r s}{1-\gamma_r s}=\frac{\gamma_r}{\gamma_r-\gamma_p}\left[\left(\frac{\beta_p\gamma_p}{k-\alpha_r\gamma_r+\beta_p\gamma_r-\alpha_p\gamma_r}\right)^{1/2}-1\right].$$
--
--   The left side is the protected group's coverage rate $\phi^{EO}_p$ at the EO thresholds of (10), so this is the closed form (52) of $\phi^{EO}_p$.
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 44, proof of Theorem 2, eqs. (48), (52)

import Mathlib
import Definitions.Def_UnfairML_Coverage_Model

namespace UnfairML.Coverage

/-- Eqs. (48), (52), p. 44: at every maximizer `s` of `πEO` on `[0, 1/(2γr)]`,
`γr s/(1 − γr s) = γr/(γr − γp) · [(βpγp/(k − αrγr + βpγr − αpγr))^{1/2} − 1]`. -/
theorem eq_52 (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k σ : ℝ)
    (hC : CostRange P k σ) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) P.sMax)
    (hmax : IsMaxOn (piEO P k) (Set.Icc 0 P.sMax) s) :
    P.γr * s / (1 - P.γr * s) =
      P.γr / (P.γr - P.γp) *
        (Real.sqrt (P.βp * P.γp / (k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr)) - 1) := by sorry
end UnfairML.Coverage
