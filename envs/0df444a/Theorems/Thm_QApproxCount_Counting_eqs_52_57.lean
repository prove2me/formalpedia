-- Prove2me | Theorems.Thm_QApproxCount_Counting_eqs_52_57
-- name    : QApproxCount.Counting.eqs_52_57
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:04.949111+00:00
-- url     : https://prove2.me/theorems/faf8e89b-f3d2-4737-a4cf-a2aa84578cf5
-- title:
--   Eqs. (52), (57) — r θmin is within 0.002 of πk and r θmax is within 1.102 of πk + π/2
-- statement:
--   Let $\theta_{\min}>0$, $0<\gamma\le0.7$, and $\theta_{\max}=(1+\gamma)\theta_{\min}\le0.002$. Let $k$ be the closest integer to $\theta_{\min}/(2\Delta\theta)$, $\Delta\theta=\theta_{\max}-\theta_{\min}$, and let $r$ be the closest odd integer to $\pi k/\theta_{\min}$ (eqs. (45)–(47), ties broken upward). Then
--   $$|r\theta_{\min}-\pi k|\le0.002,\qquad \Big|r\theta_{\max}-\Big(\pi k+\frac{\pi}{2}\Big)\Big|\le1.102 .$$
--
--   So $r$ rotates the bottom of the bracket to (almost) a multiple of $\pi$ and the top to about a quarter turn further, which is what separates the two ends of the bracket.
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, p. 9, eqs. (52) and (57) (proof of Lemma 2)

import Mathlib
import Definitions.Def_QApproxCount_Counting_Algorithm

namespace QApproxCount.Counting

/-- Eqs. (52) and (57), p. 9: let `0 < θmin`, `0 < γ ≤ 0.7`, `θmax = (1 + γ) θmin ≤ 0.002`,
and let `k`, `r` be computed by (45)–(47) (`rotK`, `rotR`). Then
`|r θmin - πk| ≤ 0.002` and `|r θmax - (πk + π/2)| ≤ 1.102`. -/
theorem eqs_52_57 (θmin θmax γ : ℝ) (hθmin : 0 < θmin) (hγ : 0 < γ) (hγ1 : γ ≤ 0.7)
    (hmax : θmax = (1 + γ) * θmin) (hθmax : θmax ≤ 0.002) :
    |(rotR θmin θmax : ℝ) * θmin - Real.pi * (rotK θmin θmax : ℝ)| ≤ 0.002 ∧
      |(rotR θmin θmax : ℝ) * θmax - (Real.pi * (rotK θmin θmax : ℝ) + Real.pi / 2)| ≤ 1.102 := by sorry

end QApproxCount.Counting
