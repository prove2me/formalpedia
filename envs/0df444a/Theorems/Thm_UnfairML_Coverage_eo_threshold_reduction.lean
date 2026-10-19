-- Prove2me | Theorems.Thm_UnfairML_Coverage_eo_threshold_reduction
-- name    : UnfairML.Coverage.eo_threshold_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:26.043481+00:00
-- url     : https://prove2.me/theorems/4adb7861-c2f5-4f7d-970b-b7459e086b2a
-- title:
--   Eq. (10) and case (1), p. 17 — under equal opportunity the optimal thresholds are (1 − γr s(1 − γp s)/(1 − γr s), 1 − γr s) and the profit is πEO(s)
-- statement:
--   Work in the model of §3 under the standing assumptions and case (1), $\beta_p\le\alpha_p+\alpha_r$. Fix any cost parameter $k$ and an effort $s\in[0,1/(2\gamma_r)]$. Then:
--
--   1. the thresholds
--   $$c^{EO}_p=1-\frac{\gamma_r s(1-\gamma_p s)}{1-\gamma_r s},\qquad c^{EO}_r=1-\gamma_r s$$
--   lie in $[0,1]$ and satisfy the equal-opportunity constraint (6);
--   2. their profit (1) equals $\pi_{EO}(s)$;
--   3. every pair $c_p,c_r\in[0,1]$ satisfying (6) has profit (1) at most $\pi_{EO}(s)$.
--
--   So, for each effort level, the EO problem reduces to maximizing $\pi_{EO}$ over effort. This is the case-(1) branch of equation (10).
--
--   **Formalization Note** When $\beta_p=\alpha_p+\alpha_r$ other thresholds satisfying (6) attain $\pi_{EO}(s)$ as well, so only optimality of the displayed pair is stated, not its uniqueness.
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 17, eq. (10) and case (1)

import Mathlib
import Definitions.Def_UnfairML_Coverage_Model

namespace UnfairML.Coverage

/-- Eq. (10) and case (1), p. 17: under equal opportunity and low expected loss, for every
effort `s ∈ [0, 1/(2γr)]` the thresholds `cp = 1 − γr s(1 − γp s)/(1 − γr s)`, `cr = 1 − γr s` are
feasible, satisfy (6) and give profit `πEO(s)`, and every feasible pair satisfying (6) gives at most
`πEO(s)`. -/
theorem eo_threshold_reduction (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) P.sMax) :
    (1 - P.γr * s * (1 - P.γp * s) / (1 - P.γr * s)) ∈ Set.Icc (0 : ℝ) 1 ∧
    (1 - P.γr * s) ∈ Set.Icc (0 : ℝ) 1 ∧
    EOConstraint P (1 - P.γr * s * (1 - P.γp * s) / (1 - P.γr * s)) (1 - P.γr * s) s ∧
    profit P k (1 - P.γr * s * (1 - P.γp * s) / (1 - P.γr * s)) (1 - P.γr * s) s = piEO P k s ∧
    ∀ cp cr : ℝ, cp ∈ Set.Icc (0 : ℝ) 1 → cr ∈ Set.Icc (0 : ℝ) 1 → EOConstraint P cp cr s →
      profit P k cp cr s ≤ piEO P k s := by sorry
end UnfairML.Coverage
