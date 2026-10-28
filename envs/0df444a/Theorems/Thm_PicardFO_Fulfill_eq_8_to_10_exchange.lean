-- Prove2me | Theorems.Thm_PicardFO_Fulfill_eq_8_to_10_exchange
-- name    : PicardFO.Fulfill.eq_8_to_10_exchange
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:39.795154+00:00
-- url     : https://prove2.me/theorems/104aa37a-7977-4ffa-a4c4-648d5a90531e
-- title:
--   Eqs. (8)–(10) (corrected: whole-unit gaps) — replacing the sequential state by a dominating process state moves π only to exhausted or overstocked nodes
-- statement:
--   Let $\pi$ be a feasible FO policy satisfying Inventory Independence, Consistency and Monotonicity. Let $s = (x, c)$ and $s' = (x', c')$ be two states, $\omega$ an order for product $i = i(\omega)$, and $Q \subseteq [J]$ a set of nodes such that
--
--   1. $c_j \le 0$ for $j \in Q$ and $c_j > 0$ for $j \notin Q$;
--   2. for every $j \notin Q$, $c'_j - c_j$ and $x'_{i,j} - x_{i,j}$ are natural numbers.
--
--   The inventories of other products and the inventory and capacity of $s'$ at the nodes of $Q$ are arbitrary. Then
--   $$
--   \pi(s', \omega) \in \{\pi(s, \omega)\} \,\cup\, Q \,\cup\, \{\, j \notin Q : x'_{i,j} > x_{i,j} \,\}.
--   $$
--
--   In the proof of Lemma A.1, $s$ is the sequential state and $s'$ the state of a process before the current order: the process's capacities and inventories dominate the sequential ones at the nodes that have not run out, by whole units. The statement says that a process's decision can differ from the sequential one only by going to a node that has run out sequentially or to a node where the process holds strictly more inventory of the ordered product.
--
--   **Formalization Note** The paper's step (8) rewrites $\pi$ as a function of the indicators $1(c_j > 0)$ "following … Assumption 3"; over real capacities Assumption 3 only gives invariance under whole-unit increments of a positive capacity, so the natural-number gaps are the hypothesis under which the chain (8)–(10) is valid. Along every run of the FO problem these gaps are integers, since all capacities and inventories start equal and move by units. $Q$ is a parameter characterised by hypothesis 1. Actions are `Option (Fin J)`, `none` being the paper's action $0$.
--
--   Differences from the source:
--   - correction: (8) "π depends on c only through 1(c_j > 0), following Assumption 3" and (6)–(7) "c^{k,m} ≥ c^{seq}, x^{k,m} ≥ x^{seq} off Q_{t_c}" → hypotheses that for j ∉ Q the gaps c′_j − c_j and x′_{i,j} − x_{i,j} are natural numbers; reason: over ℝ Assumption 3 gives invariance only under whole-unit increments, and the printed step is false with real gaps. Counterexample satisfying Assumptions 1–3 and feasibility: I = 1, J = 2, π = "among feasible nodes the one with the largest fractional part of c_j, ties to the lower index, else 0"; s: x = (1, 1), c = (1/2, 1/2), so π(s) = node 1 and Q = ∅; s′: x′ = x, c′ = (1/2, 3/5) ≥ c, so π(s′) = node 2, which is neither π(s), nor in Q, nor a node with x′ > x. Along the runs of the proof the gaps are natural numbers, so the corrected step is all the proof needs.
--   - reading: the chain of displays (8), (9), (10) and the final membership → the final membership, for which (8)–(10) are intermediate steps; reason: the final display is what the passage establishes and what (5) uses.
--   - generalization: the sequential state before t_c, the state of process m, and Q_{t_c} = {j | c^{seq}_{t_c−1,j} = 0} → arbitrary states s, s′ and any Q equal to the set of nodes of s with non-positive capacity; reason: specializes with s = the sequential state, s′ = the process state, Q = {j : c^{seq}_{t_c−1,j} ≤ 0}.
--   - reading: Assumption 2 with j′ arbitrary → j′ ≠ π((x, c), ω); reason: read literally only the never-fulfilling policy satisfies it, which makes the statement vacuous; the chosen reading is the weaker hypothesis.
--   - reading: Assumption 3's first clause for every decision j → for decisions j ∈ [J], second clause for every decision including 0; reason: e_{i,0} is undefined.
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, p. 13, eqs. (8)–(10) and the display after (10), proof of Lemma A.1

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Model

namespace PicardFO.Fulfill

/-- Eqs. (8)–(10) (p. 13), the policy exchange step: let `s` be a state whose non-positive
capacity nodes are exactly `Qs`, and let `s'` have, at every node `j ∉ Qs`, a capacity and an
inventory of product `i = prod w` exceeding those of `s` by whole units. Then `π s' w` is
`π s w`, or a node of `Qs`, or a node outside `Qs` where `s'` holds strictly more inventory of
`i` than `s`. -/
theorem eq_8_to_10_exchange {I J : ℕ} {Ω : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J))
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π)
    (s s' : State I J) (w : Ω) (Qs : Finset (Fin J))
    (hQ : ∀ j ∈ Qs, s.c j ≤ 0) (hQc : ∀ j ∉ Qs, 0 < s.c j)
    (hc : ∀ j ∉ Qs, ∃ n : ℕ, s'.c j = s.c j + n)
    (hx : ∀ j ∉ Qs, ∃ n : ℕ, s'.x (prod w) j = s.x (prod w) j + n) :
    π s' w = π s w ∨
      ∃ j, π s' w = some j ∧ (j ∈ Qs ∨ (j ∉ Qs ∧ s.x (prod w) j < s'.x (prod w) j)) := by sorry

end PicardFO.Fulfill
