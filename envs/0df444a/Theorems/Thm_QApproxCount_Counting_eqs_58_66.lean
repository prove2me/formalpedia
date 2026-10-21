-- Prove2me | Theorems.Thm_QApproxCount_Counting_eqs_58_66
-- name    : QApproxCount.Counting.eqs_58_66
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:21.198245+00:00
-- url     : https://prove2.me/theorems/e69c2212-72e7-4aba-9743-43bfa1223c44
-- title:
--   Eqs. (58)–(66) — if θmin ≤ θ ≤ θmax/(1 + 0.9γ) then −0.002 ≤ rθ − πk ≤ 0.27 and sin²(rθ) ≤ 7.5%
-- statement:
--   Let $\theta_{\min}>0$, $0<\gamma\le0.7$, $\theta_{\max}=(1+\gamma)\theta_{\min}\le0.002$, and let $k$ and $r$ be computed from $\theta_{\min},\theta_{\max}$ by eqs. (45)–(47). If
--   $$\theta_{\min}\le\theta\le\frac{\theta_{\max}}{1+0.9\gamma},$$
--   then
--   $$-0.002\le r\theta-\pi k\le0.27\qquad\text{and}\qquad\sin^2(r\theta)\le7.5\%.$$
--
--   When $\theta$ lies in the lower part of the bracket, the coin of Lemma 2 has small bias, so seeing 12% heads is unlikely.
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, pp. 9–10, eqs. (58)–(66) and the sentence after (66) (proof of Lemma 2)

import Mathlib
import Definitions.Def_QApproxCount_Counting_Algorithm

namespace QApproxCount.Counting

/-- Eqs. (58)–(66), pp. 9–10 (θ near the bottom of the bracket): with `θmin, θmax, γ, k, r` as in
Lemma 2 (`0 < θmin`, `0 < γ ≤ 0.7`, `θmax = (1 + γ) θmin ≤ 0.002`, `k = rotK`, `r = rotR`), if
`θmin ≤ θ ≤ θmax/(1 + 0.9γ)` then `-0.002 ≤ rθ - πk ≤ 0.27` and `sin²(rθ) ≤ 7.5%`. -/
theorem eqs_58_66 (θmin θmax γ θ : ℝ) (hθmin : 0 < θmin) (hγ : 0 < γ) (hγ1 : γ ≤ 0.7)
    (hmax : θmax = (1 + γ) * θmin) (hθmax : θmax ≤ 0.002)
    (hlo : θmin ≤ θ) (hhi : θ ≤ θmax / (1 + 0.9 * γ)) :
    -0.002 ≤ (rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ) ∧
      (rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ) ≤ 0.27 ∧
      Real.sin ((rotR θmin θmax : ℝ) * θ) ^ 2 ≤ 0.075 := by sorry

end QApproxCount.Counting
