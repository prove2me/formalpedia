-- Prove2me | Theorems.Thm_ProblemSpec_Equilibrium_eq_A_2_A_3
-- name    : ProblemSpec.Equilibrium.eq_A_2_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:39.709897+00:00
-- url     : https://prove2.me/theorems/349d49b7-9097-4066-85b8-4f2a982d3a42
-- title:
--   (A.2)–(A.3), App. p. 1 — every symmetric equilibrium given N is (r∗(N), m∗(N))
-- statement:
--   Fix $N>1$ participants, $S_r,S_g\ge0$, and assume $\bar r(N)\ge0$ (the page's "$w$ is not trivially small"). If $(r,m)$ is a symmetric pure-strategy equilibrium of the designers' game (no participant gains from any deviation $(r_i,m_i)$ with $r_i\ge0$, $m_i>0$), then
--   $$r=r^*(N)=\begin{cases}\bar r^g,& S_r<\bar r^g\ \text{(Region 0)},\\ S_r,&\bar r^g\le S_r\le\bar r\ \text{(Region I)},\\ \bar r,& S_r>\bar r\ \text{(Region II)},\end{cases}\qquad m=m^*(N)=\frac{A(N-1)}{N^2h(S_g)}.$$
--
--   This is the uniqueness half of the equilibrium characterization in Theorem 1, at a given number of participants.
--
--   **Formalization Note** Region 0 requires the argument of the logarithm in $\bar r^g$ to be positive; otherwise the formula is undefined and no designer guesses. Only uniqueness is stated: the paper's claim that $(r^*,m^*)$ is always an equilibrium fails for some admissible parameters (see the mission description).
-- source:
--   Jiang, Huang & Beil, The Role of Problem Specification in Crowdsourcing Contests for Design Problems, SSRN 3260862 (version of 30 Oct 2019), App. p. 1 (PDF 29), (A.2) and (A.3)

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace ProblemSpec.Equilibrium

/-- (A.2)–(A.3), App. p. 1 (PDF 29). With `N > 1` participants, `Sr, Sg ≥ 0` and `r̄(N) ≥ 0`
("w is not trivially small", p. 9), every symmetric pure-strategy equilibrium `(r, m)` of the
designers' game is `r = r∗(N)` of (A.2) and `m = m∗(N) = A(N−1)/(N² h(Sg))` of (A.3). -/
theorem eq_A_2_A_3 (P : Params) (hP : P.Standing) (Sr Sg N r m : ℝ) (hSr : 0 ≤ Sr)
    (hSg : 0 ≤ Sg) (hN : 1 < N) (hrbar : 0 ≤ rbar P N) (heq : IsSymEq P Sr Sg N r m) :
    r = rstar P N Sr ∧ m = mstar P Sg N := by sorry

end ProblemSpec.Equilibrium
