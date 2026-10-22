-- Prove2me | Theorems.Thm_ProblemSpec_Equilibrium_eq_A_3
-- name    : ProblemSpec.Equilibrium.eq_A_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:41.202638+00:00
-- url     : https://prove2.me/theorems/403a75f1-5ce1-4c5d-949a-3c611b8801e5
-- title:
--   (A.3), App. p. 1 — trial-effort first-order condition and m∗(N) = A(N−1)/(N²c₃)
-- statement:
--   Fix $N>1$ participants, $S_g\ge0$, and a symmetric profile in which every designer plays $(r,m)$ with $m>0$. A participant's expected utility $\Pr(i\text{ wins})\cdot A-C_i(r,m_i)$, as a function of her own number of trials $m_i$, is differentiable at $m_i=m$ with derivative
--   $$A\,\frac{(N-1)\,m}{(mN)^2}-c_3,\qquad c_3=h(S_g),$$
--   and this derivative vanishes if and only if
--   $$m=m^*(N)=\frac{A(N-1)}{N^2c_3}.$$
--
--   This is the first-order condition that pins down the equilibrium trial effort.
-- source:
--   Jiang, Huang & Beil, The Role of Problem Specification in Crowdsourcing Contests for Design Problems, SSRN 3260862 (version of 30 Oct 2019), App. p. 1 (PDF 29), (A.3)

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace ProblemSpec.Equilibrium

/-- (A.3), App. p. 1 (PDF 29). At a symmetric profile (`ri = r`, `mi = m > 0`, `N > 1`), a
participant's expected utility is differentiable in her number of trials `mi` at `mi = m`, with
derivative `A (N−1) m / (m N)² − c3`, `c3 = h(Sg)`; this derivative vanishes exactly when
`m = m∗(N) = A(N−1)/(N² c3)`. -/
theorem eq_A_3 (P : Params) (hP : P.Standing) (Sr Sg N r m : ℝ) (hSg : 0 ≤ Sg) (hN : 1 < N)
    (hm : 0 < m) :
    HasDerivAt (fun x => payoff P Sr Sg N r x r m)
        (P.A * ((N - 1) * m / (m * N) ^ 2) - P.h Sg) m ∧
      (P.A * ((N - 1) * m / (m * N) ^ 2) - P.h Sg = 0 ↔ m = mstar P Sg N) := by sorry

end ProblemSpec.Equilibrium
