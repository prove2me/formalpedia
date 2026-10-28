-- Prove2me | Theorems.Thm_ProblemSpec_Equilibrium_eq_A_5
-- name    : ProblemSpec.Equilibrium.eq_A_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:25.862272+00:00
-- url     : https://prove2.me/theorems/769c84cd-dab7-49b3-951b-7b1cfab35473
-- title:
--   (A.5), App. p. 1 — Region I: indifference ⇔ N = √(A/(s + c₁S_r + c₂(1/p)^{S_r}))
-- statement:
--   Let $N>1$, $S_r,S_g\ge0$, and suppose that at $N$ participants designers incorporate all and only the disclosed objectives, $r^*(N)=S_r$ (Region I). Then the indifference condition $\Pr(i\text{ wins})\cdot A-C_i(S_r,m^*)=s$ holds if and only if
--   $$N=N_1^*=\sqrt{\frac{A}{s+c_1S_r+c_2(1/p)^{S_r}}}.$$
--
--   This gives the closed form of the free-entry level in Region I.
-- source:
--   Jiang, Huang & Beil, The Role of Problem Specification in Crowdsourcing Contests for Design Problems, SSRN 3260862 (version of 30 Oct 2019), App. p. 1 (PDF 29), (A.5)

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace ProblemSpec.Equilibrium

/-- (A.5), App. p. 1 (PDF 29), Region I. If at `N > 1` participants designers incorporate all
and only the disclosed objectives (`r∗(N) = Sr`), the indifference condition
`Pr(i wins) · A − C(Sr, m∗) = s` holds exactly when
`N = N∗1 = √(A / (s + c1 Sr + c2 (1/p)^{Sr}))`. -/
theorem eq_A_5 (P : Params) (hP : P.Standing) (Sr Sg N : ℝ) (hSr : 0 ≤ Sr) (hSg : 0 ≤ Sg)
    (hN : 1 < N) (hI : rstar P N Sr = Sr) :
    entryUtility P Sr Sg N = P.s ↔ N = N1closed P Sr := by sorry

end ProblemSpec.Equilibrium
