-- Prove2me | Theorems.Thm_QApproxCount_Counting_eqs_68_74
-- name    : QApproxCount.Counting.eqs_68_74
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:34.910722+00:00
-- url     : https://prove2.me/theorems/45f7e840-9b6a-47b3-9598-7ac7ece4857c
-- title:
--   Eqs. (68)–(74) — if θmin(1 + 0.9γ) ≤ θ ≤ θmax then 0.42 ≤ rθ − πk ≤ 2.68 and sin²(rθ) ≥ 16.5%
-- statement:
--   Let $\theta_{\min}>0$, $0<\gamma\le0.7$, $\theta_{\max}=(1+\gamma)\theta_{\min}\le0.002$, and let $k$ and $r$ be computed from $\theta_{\min},\theta_{\max}$ by eqs. (45)–(47). If
--   $$\theta_{\min}(1+0.9\gamma)\le\theta\le\theta_{\max},$$
--   then
--   $$0.42\le r\theta-\pi k\le2.68\qquad\text{and}\qquad\sin^2(r\theta)\ge16.5\%.$$
--
--   When $\theta$ lies in the upper part of the bracket, the coin of Lemma 2 has bias well above 12%, so seeing too few heads is unlikely.
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, p. 10, eqs. (68)–(74) and the sentence after (74) (proof of Lemma 2)

import Mathlib
import Definitions.Def_QApproxCount_Counting_Algorithm

namespace QApproxCount.Counting

/-- Eqs. (68)–(74), p. 10 (θ near the top of the bracket): with `θmin, θmax, γ, k, r` as in
Lemma 2 (`0 < θmin`, `0 < γ ≤ 0.7`, `θmax = (1 + γ) θmin ≤ 0.002`, `k = rotK`, `r = rotR`), if
`θmin (1 + 0.9γ) ≤ θ ≤ θmax` then `0.42 ≤ rθ - πk ≤ 2.68` and `sin²(rθ) ≥ 16.5%`. -/
theorem eqs_68_74 (θmin θmax γ θ : ℝ) (hθmin : 0 < θmin) (hγ : 0 < γ) (hγ1 : γ ≤ 0.7)
    (hmax : θmax = (1 + γ) * θmin) (hθmax : θmax ≤ 0.002)
    (hlo : θmin * (1 + 0.9 * γ) ≤ θ) (hhi : θ ≤ θmax) :
    0.42 ≤ (rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ) ∧
      (rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ) ≤ 2.68 ∧
      0.165 ≤ Real.sin ((rotR θmin θmax : ℝ) * θ) ^ 2 := by sorry

end QApproxCount.Counting
