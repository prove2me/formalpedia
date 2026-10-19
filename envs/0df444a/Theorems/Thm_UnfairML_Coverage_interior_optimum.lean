-- Prove2me | Theorems.Thm_UnfairML_Coverage_interior_optimum
-- name    : UnfairML.Coverage.interior_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:28.154978+00:00
-- url     : https://prove2.me/theorems/af844cb2-227d-46ae-9fcb-59a089fe167c
-- title:
--   §4.4, p. 23 — for k in the assumed range the optimal efforts exist and are positive, and sEO < 1/(2γr)
-- statement:
--   Work in the model of §3 under the standing assumptions and case (1), with $\tau(s)=ks/(1-\gamma_r s)$ and $k$ in the range of p. 23 ($k=\alpha_r\gamma_r+\sigma^2A$, $\sigma\in[\rho,1)$). Then:
--
--   1. $\pi_{ET}$ attains its maximum on $[0,1/(2\gamma_r)]$, and every maximizer $s^{ET}$ satisfies $0<s^{ET}\le 1/(2\gamma_r)$;
--   2. $\pi_{EO}$ attains its maximum on $[0,1/(2\gamma_r)]$, and every maximizer $s^{EO}$ satisfies
--   $$0<s^{EO}<\frac{1}{2\gamma_r}.$$
--
--   In the paper's words, neither market failure (no learning) nor perfect separation happens.
--
--   **Formalization Note** The page states $0<s^{ET},s^{EO}<1/(2\gamma_r)$. At the endpoint $\sigma=\rho$ of the assumed range the ET maximizer is exactly $1/(2\gamma_r)$, so for $s^{ET}$ only the non-strict upper bound holds; this is a labelled correction.
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 23, §4.4

import Mathlib
import Definitions.Def_UnfairML_Coverage_Model

namespace UnfairML.Coverage

/-- §4.4, p. 23: for `k` in the range of p. 23, `πET` and `πEO` attain their maximum on
`[0, 1/(2γr)]`; every maximizer of `πET` is positive, and every maximizer of `πEO` lies in the open
interval `(0, 1/(2γr))`. (The page claims `sET < 1/(2γr)` as well; this fails at `σ = ρ`.) -/
theorem interior_optimum (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k σ : ℝ)
    (hC : CostRange P k σ) :
    (∃ s ∈ Set.Icc (0 : ℝ) P.sMax, IsMaxOn (piET P k) (Set.Icc 0 P.sMax) s) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) P.sMax, IsMaxOn (piET P k) (Set.Icc 0 P.sMax) s →
      0 < s ∧ s ≤ P.sMax) ∧
    (∃ s ∈ Set.Icc (0 : ℝ) P.sMax, IsMaxOn (piEO P k) (Set.Icc 0 P.sMax) s) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) P.sMax, IsMaxOn (piEO P k) (Set.Icc 0 P.sMax) s →
      0 < s ∧ s < P.sMax) := by sorry
end UnfairML.Coverage
