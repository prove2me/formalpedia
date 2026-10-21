-- Prove2me | Theorems.Thm_ProblemSpec_Equilibrium_sym_win_prob_entry_utility
-- name    : ProblemSpec.Equilibrium.sym_win_prob_entry_utility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:32.320366+00:00
-- url     : https://prove2.me/theorems/b610b749-e0c5-4faf-95f8-b2a140b0cd8f
-- title:
--   App. p. 1 and p. 10 — Pr(i wins) = 1/N, and the entry utility does not involve c₃ = h(S_g)
-- statement:
--   Let $N>1$ and $S_g\ge0$.
--
--   1. In a symmetric profile in which all designers play $(r,m)$ with $m>0$, $\Pr(i\text{ wins})=1/N$.
--   2. When all $N$ participants play $(r^*(N),m^*(N))$, a participant's expected utility is
--   $$U(N;S_r)=\frac{A}{N^2}-c_g\,(r^*-S_r)^+-c_1S_r-c_2\,(1/p)^{r^*},\qquad r^*=r^*(N).$$
--
--   The right-hand side does not involve the trial cost $c_3=h(S_g)$: designers scale their trials to $c_3$, so the total trial cost $c_3m^*=A(N-1)/N^2$ is the same for every $S_g$, and execution guidance does not affect entry.
-- source:
--   Jiang, Huang & Beil, The Role of Problem Specification in Crowdsourcing Contests for Design Problems, SSRN 3260862 (version of 30 Oct 2019), App. p. 1 (PDF 29), 'In a symmetric equilibrium, Pr(i wins) = 1/N'; p. 10 (PDF 10), second paragraph

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace ProblemSpec.Equilibrium

/-- App. p. 1 (PDF 29) and p. 10 (PDF 10). In a symmetric profile with `N > 1` participants the
win probability is `1/N`; and the expected utility of a participant when all play
`(r∗(N), m∗(N))` is `A/N² − cg (r∗ − Sr)⁺ − c1 Sr − c2 (1/p)^{r∗}`, which does not involve `h`
(the trial cost `c3 = h(Sg)`). -/
theorem sym_win_prob_entry_utility (P : Params) (hP : P.Standing) (Sr Sg N : ℝ) (hSg : 0 ≤ Sg)
    (hN : 1 < N) :
    (∀ r m : ℝ, 0 < m → winProb P Sr N r m r m = 1 / N) ∧
      entryUtility P Sr Sg N =
        P.A / N ^ 2 - P.cg * max (rstar P N Sr - Sr) 0 - P.c1 * Sr
          - P.c2 * (1 / P.p) ^ rstar P N Sr := by sorry

end ProblemSpec.Equilibrium
