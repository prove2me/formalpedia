-- Prove2me | Theorems.Thm_UnfairML_Coverage_et_threshold_reduction
-- name    : UnfairML.Coverage.et_threshold_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:31.658799+00:00
-- url     : https://prove2.me/theorems/87167ee4-3784-4822-be73-557fceff79d5
-- title:
--   Eq. (4) and case (1), pp. 15, 17 — under equal treatment the optimal common threshold is 1 − γr s and the profit is πET(s)
-- statement:
--   Work in the model of §3 under the standing assumptions and case (1), $\beta_p\le\alpha_p+\alpha_r$. Fix any cost parameter $k$, an effort $s\in[0,1/(2\gamma_r)]$ and a common threshold $c\in[0,1]$ for both groups (equal treatment). Then the profit (1) satisfies
--   $$\pi(c,c,s)\le\pi_{ET}(s),$$
--   with equality if and only if $c=1-\gamma_r s$.
--
--   So, for each effort level, the bank's best threshold under equal treatment is $c^{ET}_p=c^{ET}_r=1-\gamma_r s$, and the ET problem reduces to maximizing $\pi_{ET}$ over effort. This is the case-(1) branch of equation (4).
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 15, eq. (4), and p. 17, case (1)

import Mathlib
import Definitions.Def_UnfairML_Coverage_Model

namespace UnfairML.Coverage

/-- Eq. (4) and case (1), pp. 15, 17: under equal treatment and low expected loss, for every
effort `s ∈ [0, 1/(2γr)]` the profit (1) at a common threshold `c ∈ [0, 1]` is at most `πET(s)`, with
equality exactly at `c = 1 − γr s`. -/
theorem et_threshold_reduction (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k s c : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) P.sMax) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    profit P k c c s ≤ piET P k s ∧ (profit P k c c s = piET P k s ↔ c = 1 - P.γr * s) := by sorry
end UnfairML.Coverage
