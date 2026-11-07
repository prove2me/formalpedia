-- Prove2me | Theorems.Thm_SendSplit_Existence_five_implies_six
-- name    : SendSplit.Existence.five_implies_six
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-07T01:12:24.937855+00:00
-- url     : https://prove2.me/theorems/f2fd2f8a-4949-4c49-a64b-b5a6d9812dbc
-- title:
--   Theorem 1, 5° ⇒ 6° — nonnegative circuit slopes give minimum-cost chains to $\nu$ in the augmented graph
-- statement:
--   Let $G=(N,A)$ be a graph with arc cost functions $c_{ij}$, and write $\dot c_{ij}(\infty)=\lim_{t\to\infty}\dot c_{ij}(t)\in[-\infty,\infty)$ for the limiting right-derivative (`slopeAtInfty`). Suppose condition 5° of Theorem 1 holds:
--
--   $$\sum_{(i,j)\in C}\dot c_{ij}(\infty)\ \ge\ 0\quad\text{for every simple circuit of } G \text{ with arc set } C.$$
--
--   Let $S$ contain exactly one node of each sink strong component of $G$ and no other node, and form the augmented graph $\underline G$ by appending a node $\nu$ and arcs $(i,\nu)$, $i\in S$. Give $\underline G$ the arc costs $\underline c$: $\underline c_{ij}=\dot c_{ij}(\infty)$ for arcs inside a strong component of $G$, an arbitrary real $b_{ij}$ for arcs of $G$ joining distinct strong components, and an arbitrary real $b^\nu_i$ for the appended arcs $(i,\nu)$. Then from every node $u$ of $\underline G$ (including $\nu$ itself) there is a minimum-cost chain to $\nu$: a chain (directed walk) of real cost whose cost is at most that of every chain from $u$ to $\nu$.
--
--   This is the implication 5° ⇒ 6° of Theorem 1: the circuit condition 5°, which does not involve demands, yields the shortest-chain test 6° and the potentials $\underline\pi$ used for 7°.
--
--   **Formalization Note.** Chains are walks (lists of nodes of $\underline G$, `none` standing for $\nu$) and may repeat nodes; costs live in $[-\infty,\infty]$ (`EReal`); "minimum-cost" means attained, with real cost.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 639, Theorem 1 (the equivalence of conditions 5° and 6°)

import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_AugmentedGraph

namespace SendSplit.Existence

theorem five_implies_six {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (h5 : ∀ C, IsSimpleCircuit G C → 0 ≤ ∑ p ∈ C, slopeAtInfty (c p.1 p.2))
    (S : Finset (Fin n)) (hS : IsSinkSelection G S) (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ)
    (u : Option (Fin n)) :
    HasMinCostChain G S (augCost G c b bν) u := by sorry

end SendSplit.Existence
