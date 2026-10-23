-- Prove2me | Theorems.Thm_RiskyBenefitCost_NthDegree_display_8
-- name    : RiskyBenefitCost.NthDegree.display_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:10.956238+00:00
-- url     : https://prove2.me/theorems/7e448574-54a9-49d2-8056-21f3247bddaa
-- title:
--   Display (8), p. 3628 (PDF 5) — the bracket of (7) rewritten with r_{N+1}, and it is negative
-- statement:
--   Let $N\ge1$, $z_0\ge0$, and let $w$ be a point where the decision maker is strictly $N$th-degree risk averse, $(-1)^{N+1}U^{(N)}(w)>0$, $(N+1)$th-degree risk averse, $(-1)^{N+2}U^{(N+1)}(w)\ge0$, and has relative $(N+1)$th-degree risk aversion $r_{N+1}(w)=-wU^{(N+1)}(w)/U^{(N)}(w)$ below $N$. Put $t=w-z_0$. Then the bracket of display (7) satisfies
--   $$t\,(-1)^{N+2}U^{(N+1)}(w)-N(-1)^{N+1}U^{(N)}(w)=(-1)^{N+1}U^{(N)}(w)\,\big[r_{N+1}(w)-N\big]-z_0(-1)^{N+2}U^{(N+1)}(w),$$
--   and this quantity is strictly negative.
--
--   The first term on the right is negative because $r_{N+1}<N$, the second is non-positive because $z_0\ge0$ and $U$ is $(N+1)$th-degree risk averse. This sign is what makes (5) monotone in $b$ in every problem class.
--
--   **Formalization Note.** In the paper's notation $w=f(b)(X-x_0)+z_0$, so $t=f(b)(X-x_0)$, and the page's "$t+z_0$" is $w$. Two printed slips are corrected: the page writes $t=f(b)(X-x_0)+z_0$ (it should be without $z_0$, otherwise "$t+z_0$" would count $z_0$ twice), and $r_N$ (it should be Definition 4's $r_{N+1}$). The hypothesis $z_0\ge0$ is added: the page marks $z_0(-1)^{N+2}U^{(N+1)}$ as "$\ge0$", which assumes it silently, and without it the bracket can be positive.
-- source:
--   Menegatti & Peter, Changes in risky benefits and in risky costs: a question of the right order, Management Science 68(5) (2022), p. 3628 (PDF 5), display (8) and 'This is negative under our assumptions'

import Mathlib
import Definitions.Def_RiskyBenefitCost_NthDegree_Model

namespace RiskyBenefitCost.NthDegree

theorem display_8 (N : ℕ) (hN : 1 ≤ N) (U : ℝ → ℝ) (z0 w : ℝ) (hz0 : 0 ≤ z0)
    (hRA_N : 0 < (-1 : ℝ) ^ (N + 1) * iteratedDeriv N U w)
    (hRA_N1 : 0 ≤ (-1 : ℝ) ^ (N + 2) * iteratedDeriv (N + 1) U w)
    (hrel : relRiskAversion N U w < N) :
    (w - z0) * (-1 : ℝ) ^ (N + 2) * iteratedDeriv (N + 1) U w
        - N * (-1 : ℝ) ^ (N + 1) * iteratedDeriv N U w
      = (-1 : ℝ) ^ (N + 1) * iteratedDeriv N U w * (relRiskAversion N U w - N)
        - z0 * (-1 : ℝ) ^ (N + 2) * iteratedDeriv (N + 1) U w ∧
    (w - z0) * (-1 : ℝ) ^ (N + 2) * iteratedDeriv (N + 1) U w
        - N * (-1 : ℝ) ^ (N + 1) * iteratedDeriv N U w < 0 := by sorry

end RiskyBenefitCost.NthDegree
