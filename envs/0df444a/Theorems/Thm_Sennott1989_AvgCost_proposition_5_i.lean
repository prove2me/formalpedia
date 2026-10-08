-- Prove2me | Theorems.Thm_Sennott1989_AvgCost_proposition_5_i
-- name    : Sennott1989.AvgCost.proposition_5_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:35.059136+00:00
-- url     : https://prove2.me/theorems/3b211337-6000-497f-85d1-ffe4cad0c1c3
-- title:
--   Proposition 5 (i), p. 629 — a stationary policy inducing an irreducible ergodic chain with finite mean cost implies Assumptions 1 and 3
-- statement:
--   Consider a Markov decision chain on $0,1,2,\dots$ with finite action sets and nonnegative costs. Assume it has a stationary policy $f$ whose induced Markov chain (transition probabilities $P_{ij}(f(i))$) is irreducible and ergodic and satisfies any of the three equivalent conditions of Proposition 4 with the cost $c(i)=C(i,f(i))$. Then Assumption 1 and Assumption 3 hold: $V_\alpha(i)<\infty$ for all $i$ and $\alpha\in(0,1)$, and there are bounds $M_i\ge0$ with $h_\alpha(i)\le M_i$ for all $i,\alpha$ and, for each $i$, an action $a(i)$ with $\sum_jP_{ij}(a(i))M_j<\infty$.
--
--   Together with Assumption 2 this puts the Theorem within reach of a single well-behaved stationary policy.
-- source:
--   Sennott, Average Cost Optimal Stationary Policies in Infinite State Markov Decision Processes with Unbounded Costs, Oper. Res. 37(4):626–633 (1989), DOI 10.1287/opre.37.4.626, §2, Proposition 5 (i), p. 629

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott1989.AvgCost

open SennottDP.Discounted

/-- Sennott (1989), §2, Proposition 5 (i), p. 629. Assume the Markov decision process has a
stationary policy `f` inducing an irreducible, ergodic Markov chain satisfying any of the three
conditions of Proposition 4 (with the cost `c(i) = C(i, f(i))`). Then Assumptions 1 and 3 hold.

**Formalization Note** The hypothesis is `GoodPolicy M f`: the chain with transition
probabilities `P_{ij}(f(i))` is irreducible with every state positive recurrent, and satisfies
condition (i), (ii) or (iii) of Proposition 4. "Assumption 3 holds" is `∃ Mb, Assumption3 M Mb`. -/
theorem proposition_5_i {Act : Type} (M : MDC ℕ Act) (f : StationaryPolicy M)
    (hf : GoodPolicy M f) :
    Assumption1 M ∧ ∃ Mb : ℕ → ℝ, Assumption3 M Mb := by sorry

end Sennott1989.AvgCost
