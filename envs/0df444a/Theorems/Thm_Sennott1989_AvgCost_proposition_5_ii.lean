-- Prove2me | Theorems.Thm_Sennott1989_AvgCost_proposition_5_ii
-- name    : Sennott1989.AvgCost.proposition_5_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:32.005072+00:00
-- url     : https://prove2.me/theorems/192ea318-8758-4c37-bd84-d8296e8fa29c
-- title:
--   Proposition 5 (ii), p. 629 — if every (state, action) pair is used by a policy as in (i), then Assumption 3* holds
-- statement:
--   Consider a Markov decision chain on $0,1,2,\dots$ with finite action sets and nonnegative costs. Suppose that for each state $i$ and each action $a\in A_i$ there is a stationary policy $f_{i,a}$ with $f_{i,a}(i)=a$ that satisfies the hypotheses of Proposition 5 (i) (its induced chain is irreducible, ergodic and satisfies one of the conditions of Proposition 4 with its own costs). Then Assumption 3\* holds: there are bounds $M_i\ge0$ satisfying Assumption 3 such that $\sum_jP_{ij}(a)M_j<\infty$ for every $i$ and every $a\in A_i$.
--
--   This is the route to the optimality equation (6) in the application.
--
--   **Formalization Note** The conclusion also records Assumption 1, which part (i) already gives under these hypotheses; Assumption 3\* is phrased through $h_\alpha(i)=V_\alpha(i)-V_\alpha(0)$, which the paper uses only under Assumption 1.
-- source:
--   Sennott, Average Cost Optimal Stationary Policies in Infinite State Markov Decision Processes with Unbounded Costs, Oper. Res. 37(4):626–633 (1989), DOI 10.1287/opre.37.4.626, §2, Proposition 5 (ii), p. 629

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott1989.AvgCost

open SennottDP.Discounted

/-- Sennott (1989), §2, Proposition 5 (ii), p. 629. If for each state `i` and each action
`a ∈ A_i` there is a stationary policy `f_{i,a}` that chooses action `a` in state `i` and satisfies
the assumptions of part (i), then Assumption 3* holds.

**Formalization Note** The conclusion also states Assumption 1, which part (i) already gives under
the same hypotheses: Assumption 3* is stated through `h_α(i) = V_α(i) − V_α(0)`, which the paper
defines only under Assumption 1 (see `relValue`). -/
theorem proposition_5_ii {Act : Type} (M : MDC ℕ Act)
    (hfa : ∀ i : ℕ, ∀ a ∈ M.A i, ∃ f : StationaryPolicy M, f.1 i = a ∧ GoodPolicy M f) :
    Assumption1 M ∧ ∃ Mb : ℕ → ℝ, Assumption3Star M Mb := by sorry

end Sennott1989.AvgCost
