-- Prove2me | Theorems.Thm_SendSplit_DPEquations_bellman_greatest_solution
-- name    : SendSplit.DPEquations.bellman_greatest_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:13:43.852005+00:00
-- url     : https://prove2.me/theorems/48eafad7-cdf4-4db8-84a1-bfdeb6fc8c3b
-- title:
--   Eq. (2)′ — with nonnegative circuits, minimum chain costs are the greatest +∞-or-real solution of Bellman's equations, nondecreasing in the arc costs
-- statement:
--   Let $G$ be a finite directed graph without loops, with real arc costs $a_{kj}$ on its arcs and a destination node $t$ from which no arc leaves. Suppose that **every simple circuit of $G$ has nonnegative cost**. For each node $k$ let
--
--   $$\bar C_k \;=\; \inf \{ \text{cost of } P : P \text{ a chain (walk) in } G \text{ from } k \text{ to } t \},$$
--
--   with $\bar C_k = +\infty$ if there is no such chain. Then:
--
--   1. $\bar C$ is a $+\infty$ or real-valued solution of Bellman's equations $\bar C_t = 0$, $\bar C_k = \min_{(k,j)} [a_{kj} + \bar C_j]$ for $k \neq t$;
--   2. $\bar C_k$ is the **minimum** cost among all chains from $k$ to $t$: either $\bar C_k = +\infty$ or some chain from $k$ to $t$ has cost exactly $\bar C_k$;
--   3. $\bar C$ is the **greatest** such solution: $C_k \le \bar C_k$ for every $+\infty$ or real-valued solution $C$ and every $k$;
--   4. $\bar C$ is **nondecreasing in the arc costs**: if $G'$ has the same destination, its arcs are among those of $G$, and $a_{kj} \le a'_{kj}$ on every arc of $G'$, then $\bar C_k \le \bar C'_k$ for all $k$.
--
--   In the proof of Theorem 2 this is applied to $G'_I$, where (2) becomes (2)′; item 4 is what transfers $B'_{iI} \le B_{iI}$ to $C'_{iI} \le C_{iI}$.
--
--   **Formalization Note** Arc costs in $\mathbb{R} \cup \{+\infty\}$ are encoded by real lengths on an arc set: a cost of $+\infty$ is a missing arc. Hence "$a \le a'$" for extended costs becomes: every arc of $G'$ is an arc of $G$, with no larger cost. Chains are walks (nodes may repeat), as in the platform definition `BertsekasShortestDistance`; the paper's "as is well known" is made explicit as items 1–4.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 642, Eq. (2)′

import Mathlib
import Definitions.Def_BertsekasSPGraph
import Definitions.Def_SendSplit_DPEquations_Bellman

namespace SendSplit.DPEquations

theorem bellman_greatest_solution {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V)
    (hloop : ∀ i, (i, i) ∉ G.arcs) (hout : ∀ j, (G.t, j) ∉ G.arcs)
    (hcirc : ∀ l, IsSimpleCircuit G l → 0 ≤ circuitLength G l) :
    IsBellmanSolution G (fun k => BertsekasShortestDistance G k G.t) ∧
      (∀ k, BertsekasShortestDistance G k G.t = ⊤ ∨
        ∃ l, BertsekasIsWalkFrom G k G.t l ∧
          ((BertsekasWalkLength G l : ℝ) : EReal) = BertsekasShortestDistance G k G.t) ∧
      (∀ C : V → EReal, IsBellmanSolution G C → ∀ k, C k ≤ BertsekasShortestDistance G k G.t) ∧
      (∀ G' : BertsekasSPGraph V, G'.t = G.t → G'.arcs ⊆ G.arcs →
        (∀ p ∈ G'.arcs, G.length p.1 p.2 ≤ G'.length p.1 p.2) →
        ∀ k, BertsekasShortestDistance G k G.t ≤ BertsekasShortestDistance G' k G'.t) := by sorry

end SendSplit.DPEquations
