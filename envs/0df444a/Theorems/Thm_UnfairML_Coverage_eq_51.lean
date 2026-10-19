-- Prove2me | Theorems.Thm_UnfairML_Coverage_eq_51
-- name    : UnfairML.Coverage.eq_51
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:27.234657+00:00
-- url     : https://prove2.me/theorems/4711510c-49b5-4999-8491-be5131d3dc52
-- title:
--   Eqs. (47), (49)–(51), p. 44 — closed form of the protected coverage rate at the ET-optimal effort
-- statement:
--   Work in the model of §3 under the standing assumptions and case (1), with $\tau(s)=ks/(1-\gamma_r s)$ and $k$ in the range of p. 23. Let $s$ be any maximizer of $\pi_{ET}$ on $[0,1/(2\gamma_r)]$. Then
--   $$\frac{\gamma_r s}{1-\gamma_p s}=\frac{\gamma_r}{\gamma_r-\gamma_p}\left[1-\left(\frac{k-\alpha_r\gamma_r}{\alpha_p\gamma_r+\beta_p\gamma_p-\beta_p\gamma_r}\right)^{1/2}\right].$$
--
--   The left side is the protected group's coverage rate $\phi^{ET}_p$ at the threshold $1-\gamma_r s$, so this is the closed form (51) of $\phi^{ET}_p$.
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 44, proof of Theorem 2, eqs. (47), (49)–(51)

import Mathlib
import Definitions.Def_UnfairML_Coverage_Model

namespace UnfairML.Coverage

/-- Eqs. (47), (49)–(51), p. 44: at every maximizer `s` of `πET` on `[0, 1/(2γr)]`,
`γr s/(1 − γp s) = γr/(γr − γp) · [1 − ((k − αrγr)/(αpγr + βpγp − βpγr))^{1/2}]`. -/
theorem eq_51 (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k σ : ℝ)
    (hC : CostRange P k σ) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) P.sMax)
    (hmax : IsMaxOn (piET P k) (Set.Icc 0 P.sMax) s) :
    P.γr * s / (1 - P.γp * s) =
      P.γr / (P.γr - P.γp) * (1 - Real.sqrt ((k - P.αr * P.γr) / P.Acoef)) := by sorry
end UnfairML.Coverage
