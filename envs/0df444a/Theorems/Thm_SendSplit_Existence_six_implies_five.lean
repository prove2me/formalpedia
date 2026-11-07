-- Prove2me | Theorems.Thm_SendSplit_Existence_six_implies_five
-- name    : SendSplit.Existence.six_implies_five
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-07T01:12:35.797174+00:00
-- url     : https://prove2.me/theorems/0b28c36e-66cc-4ec3-a136-408c6620be3b
-- title:
--   Theorem 1, 6° ⇒ 5° — minimum-cost chains to $\nu$ force nonnegative circuit slopes
-- statement:
--   Let $G=(N,A)$ be a graph with arc cost functions $c_{ij}$ and limiting right-derivatives $\dot c_{ij}(\infty)\in[-\infty,\infty)$ (`slopeAtInfty`). Suppose condition 6° of Theorem 1 holds: for every set $S$ containing exactly one node of each sink strong component of $G$ and no other node, and every choice of the arc costs $\underline c$ of the augmented graph $\underline G$ ($\dot c_{ij}(\infty)$ inside strong components, arbitrary reals $b_{ij}$ on arcs joining distinct strong components and $b^\nu_i$ on the appended arcs $(i,\nu)$), there is a minimum-cost chain (of real cost) to $\nu$ from each node of $\underline G$. Then condition 5° holds:
--
--   $$\sum_{(i,j)\in C}\dot c_{ij}(\infty)\ \ge\ 0\quad\text{for every simple circuit of } G \text{ with arc set } C.$$
--
--   This is the implication 6° ⇒ 5° of Theorem 1, closing the equivalence of the circuit condition 5° and the shortest-chain test 6°.
--
--   **Formalization Note.** Chains are walks (lists of nodes of $\underline G$, `none` standing for $\nu$) and may repeat nodes; costs live in $[-\infty,\infty]$ (`EReal`); "minimum-cost" means attained, with real cost.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 639, Theorem 1 (the equivalence of conditions 5° and 6°)

import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_AugmentedGraph

namespace SendSplit.Existence

theorem six_implies_five {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (h6 : ∀ S, IsSinkSelection G S → ∀ (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ),
      ∀ u, HasMinCostChain G S (augCost G c b bν) u) :
    ∀ C, IsSimpleCircuit G C → 0 ≤ ∑ p ∈ C, slopeAtInfty (c p.1 p.2) := by sorry

end SendSplit.Existence
