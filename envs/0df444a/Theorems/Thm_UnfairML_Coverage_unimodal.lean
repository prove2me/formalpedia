-- Prove2me | Theorems.Thm_UnfairML_Coverage_unimodal
-- name    : UnfairML.Coverage.unimodal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:25.498367+00:00
-- url     : https://prove2.me/theorems/3eee51cc-dd41-40f6-bb2e-5ee8ece4d18d
-- title:
--   Proof of Theorem 1, p. 43 — for τ(s) = ks/(1 − γr s), πET and πEO are unimodal on [0, 1/(2γr)]
-- statement:
--   Work in the model of §3 under the standing assumptions and case (1), with learning cost $\tau(s)=ks/(1-\gamma_r s)$ and $k$ in the range of p. 23: $k\in[\alpha_r\gamma_r+\rho^2A,\ \alpha_r\gamma_r+A)$ and $k=\alpha_r\gamma_r+\sigma^2A$ with $\sigma\in[\rho,1)$, where $A=\alpha_p\gamma_r-\beta_p\gamma_r+\beta_p\gamma_p$ and $\rho=1/(2-\gamma_p/\gamma_r)$.
--
--   Then the reduced profits $\pi_{ET}$ and $\pi_{EO}$ are both unimodal on $[0,1/(2\gamma_r)]$: there are points $m_1,m_2\in[0,1/(2\gamma_r)]$ such that
--   $$\pi_{ET}\ \text{is strictly increasing on }[0,m_1]\text{ and strictly decreasing on }[m_1,1/(2\gamma_r)],$$
--   and likewise $\pi_{EO}$ with $m_2$.
--
--   Unimodality is what lets the first-order conditions (47)–(48) identify the optimal efforts.
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 43, proof of Theorem 1, 'It is easy to verify that for τ(s) = ks/(1−γr s), πET(s) and πEO(s) are both unimodal functions'

import Mathlib
import Definitions.Def_UnfairML_Coverage_Model

namespace UnfairML.Coverage

/-- Proof of Theorem 1, p. 43: for `τ(s) = k s/(1 − γr s)` with `k` in the range of p. 23,
`πET` and `πEO` are unimodal on `[0, 1/(2γr)]`: strictly increasing up to a point and strictly
decreasing after it. -/
theorem unimodal (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k σ : ℝ)
    (hC : CostRange P k σ) :
    (∃ m₁ ∈ Set.Icc (0 : ℝ) P.sMax,
      StrictMonoOn (piET P k) (Set.Icc 0 m₁) ∧ StrictAntiOn (piET P k) (Set.Icc m₁ P.sMax)) ∧
    (∃ m₂ ∈ Set.Icc (0 : ℝ) P.sMax,
      StrictMonoOn (piEO P k) (Set.Icc 0 m₂) ∧ StrictAntiOn (piEO P k) (Set.Icc m₂ P.sMax)) := by sorry
end UnfairML.Coverage
