-- Prove2me | Theorems.Thm_ProblemSpec_Equilibrium_marginal_win_prob
-- name    : ProblemSpec.Equilibrium.marginal_win_prob
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:23.133334+00:00
-- url     : https://prove2.me/theorems/b5d7c0a5-8e15-4101-9b7f-4dc40cc8ac13
-- title:
--   App. p. 1 — marginal winning chance in r_i at a symmetric profile
-- statement:
--   Fix $N>1$ participants and a symmetric profile in which every designer, including $i$, plays $(r,m)$ with $m>0$. Let $\Pr(i\text{ wins})$ be the logit win probability (A.1), viewed as a function of $i$'s own number of incorporated objectives $r_i$, with $m_i=m$ and the opponents fixed at $(r,m)$. Then at $r_i=r$:
--
--   1. if $S_r<r$ (designers guess), $$\frac{\partial\Pr(i\text{ wins})}{\partial r_i}=\frac{\nu w}{\mu}\cdot\frac{N-1}{N^2};$$
--   2. if $r<S_r$, $$\frac{\partial\Pr(i\text{ wins})}{\partial r_i}=\frac{w}{\mu}\cdot\frac{N-1}{N^2}.$$
--
--   These marginal winning chances, set against the marginal cost of an objective, yield the thresholds $\bar r^g$ and $\bar r$ of Theorem 1.
--
--   **Formalization Note** The derivative is a two-sided derivative (`HasDerivAt`) at an interior point of each linear piece of the baseline quality; the kink $r=S_r$ is not covered, as on the page.
-- source:
--   Jiang, Huang & Beil, The Role of Problem Specification in Crowdsourcing Contests for Design Problems, SSRN 3260862 (version of 30 Oct 2019), App. p. 1 (PDF 29), 'Equilibrium r∗' paragraph

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace ProblemSpec.Equilibrium

/-- Marginal winning chance, App. p. 1 (PDF 29). At a symmetric profile (`ri = r`, `mi = m > 0`,
`N > 1` participants) the derivative of the win probability (A.1) in `ri` is
`(νw/μ)(N−1)/N²` when `Sr < r` and `(w/μ)(N−1)/N²` when `Sr > r`. -/
theorem marginal_win_prob (P : Params) (hP : P.Standing) (Sr N r m : ℝ) (hN : 1 < N)
    (hm : 0 < m) :
    (Sr < r → HasDerivAt (fun x => winProb P Sr N x m r m)
        (P.ν * P.w / P.μ * ((N - 1) / N ^ 2)) r) ∧
    (r < Sr → HasDerivAt (fun x => winProb P Sr N x m r m)
        (P.w / P.μ * ((N - 1) / N ^ 2)) r) := by sorry

end ProblemSpec.Equilibrium
