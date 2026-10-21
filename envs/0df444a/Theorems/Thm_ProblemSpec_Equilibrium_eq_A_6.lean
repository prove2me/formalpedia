-- Prove2me | Theorems.Thm_ProblemSpec_Equilibrium_eq_A_6
-- name    : ProblemSpec.Equilibrium.eq_A_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:26.572656+00:00
-- url     : https://prove2.me/theorems/2972fd24-0a6b-4ce9-bf01-075388ffa997
-- title:
--   (A.6), App. p. 2 — Region II: indifference ⇔ N = (√(4Y(X+1)+X²) − X)/(2Y)
-- statement:
--   Let $N>1$, $S_r,S_g\ge0$, and suppose $S_r>\bar r(N)$ (Region II), so that designers incorporate only $r^*(N)=\bar r(N)$ of the disclosed objectives. Then the indifference condition $\Pr(i\text{ wins})\cdot A-C_i(\bar r,m^*)=s$ holds if and only if
--   $$N=N_2^*=\frac{\sqrt{4Y(X+1)+X^2}-X}{2Y},\qquad X=\frac{w}{\mu\ln(1/p)},\quad Y=\frac{s+c_1S_r}{A}.$$
--
--   This gives the closed form of the free-entry level in Region II.
-- source:
--   Jiang, Huang & Beil, The Role of Problem Specification in Crowdsourcing Contests for Design Problems, SSRN 3260862 (version of 30 Oct 2019), App. p. 2 (PDF 30), (A.6)

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace ProblemSpec.Equilibrium

/-- (A.6), App. p. 2 (PDF 30), Region II. If at `N > 1` participants `Sr > r̄(N)` (designers
incorporate only a subset of the disclosed objectives, `r∗(N) = r̄`), the indifference condition
`Pr(i wins) · A − C(r̄, m∗) = s` holds exactly when
`N = N∗2 = (√(4Y(X+1) + X²) − X)/(2Y)`, `X = w/(μ ln(1/p))`, `Y = (s + c1 Sr)/A`. -/
theorem eq_A_6 (P : Params) (hP : P.Standing) (Sr Sg N : ℝ) (hSr : 0 ≤ Sr) (hSg : 0 ≤ Sg)
    (hN : 1 < N) (hII : rbar P N < Sr) :
    entryUtility P Sr Sg N = P.s ↔ N = N2closed P Sr := by sorry

end ProblemSpec.Equilibrium
