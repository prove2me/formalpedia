-- Prove2me | Theorems.Thm_SendSplit_Existence_theorem1_existence_reduction
-- name    : SendSplit.Existence.theorem1_existence_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:24:43.214562+00:00
-- url     : https://prove2.me/theorems/d4801d07-7a7b-4eda-a8e8-4d491c0bdef3
-- title:
--   Theorem 1 — existence of minimum-cost flows and reduction to nonnegative arc costs
-- statement:
--   Let $G = (N, A)$ be a graph whose arc costs $c_{ij}$ are concave on $[0,\infty)$ with $c_{ij}(0) = 0$. The following are equivalent.
--
--   1. (1°) There is a minimum-cost flow for some demand vector.
--   2. (2°) The null circulation is a minimum-cost circulation.
--   3. (3°) For every demand vector $r$: if there is a flow for $r$, there is a minimum-cost flow for $r$ that is extreme.
--   4. (4°) Each simple circulation $y$ has nonnegative flow cost, $c(y) \ge 0$.
--   5. (5°) $\sum_{(i,j)\in C} \dot c_{ij}(\infty) \ge 0$ for every simple circuit of $G$ with arc set $C$.
--   6. (6°) For every set $S$ containing exactly one node of each sink strong component of $G$ and no other node, and every choice of the arc costs $\underline{c}$ of the augmented graph $\underline{G}$ ($\dot c_{ij}(\infty)$ inside strong components, arbitrary real numbers on the other arcs, including the appended arcs $(i,\nu)$), there is a minimum-cost chain to $\nu$ from each node of $\underline{G}$.
--
--   Moreover, let $r$ be a demand vector for which a flow exists, $z = \sum_i r_i^+$, and let $S$, $\underline{c}$ be as in 6° with
--
--   $$\underline{c}_{ij}\, z \le c_{ij}(z) \quad \text{for every arc } (i,j) \text{ joining distinct strong components of } G.$$
--
--   Then 1°–6° are also equivalent to
--
--   7. (7°) there is $\pi \in \mathbb{R}^n$ with $c^\pi_{ij}(x_{ij}) = c_{ij}(x_{ij}) - (\pi_i - \pi_j)x_{ij} \ge 0$ for every arc $(i,j)$ of $G$ and every flow $x$ for $r$;
--
--   and when they hold, the minimum chain costs $\underline{\pi}_i$ in $\underline{G}$ are real and $\pi = \underline{\pi}$ satisfies 7°.
--
--   The theorem characterizes when a minimum-concave-cost uncapacitated flow problem has an optimum by a condition (4° or 5°) that does not involve the demands, gives a shortest-chain test for it (6°), and produces node potentials that turn the problem into an equivalent one with nonnegative arc costs (7°), which the send-and-split method then solves.
--
--   **Formalization Note** The equivalence of 1°–6° is `List.TFAE`. "Minimum-cost" always means attained: a feasible object whose cost is $\le$ that of every feasible object. A minimum-cost chain must have real cost (see the AugmentedGraph definition). Chains are walks, not simple paths. The paper states the 7° part only with "$r$ is a demand vector"; this formalization adds the hypothesis that a flow for $r$ exists, which the paper assumes in the surrounding text ("if there is a flow"): without it 7° holds vacuously while 4° may fail (two nodes, arcs $(0,1),(1,0)$, $c_{ij}(y) = -y$, $r = (1,1)$). The inequality $\underline{\pi}_i - \underline{\pi}_j \le \cdots$ uses the real values of $\underline{\pi}$ (`EReal.toReal`), which are exact because $\underline{\pi}$ is shown real.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 639, Theorem 1

import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_ReducedCost
import Definitions.Def_SendSplit_Existence_AugmentedGraph

namespace SendSplit.Existence

theorem theorem1_existence_reduction {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) :
    List.TFAE
        [ ∃ (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ), IsMinCostFlow G c r x,
          IsMinCostFlow G c (fun _ => 0) (fun _ _ => 0),
          ∀ r : Fin n → ℝ, (∃ x, IsFlow G r x) →
            ∃ x, IsMinCostFlow G c r x ∧ IsExtremeFlow G r x,
          ∀ y, IsSimpleCirculation G y → 0 ≤ flowCost G c y,
          ∀ C, IsSimpleCircuit G C → 0 ≤ ∑ p ∈ C, slopeAtInfty (c p.1 p.2),
          ∀ S, IsSinkSelection G S → ∀ (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ),
            ∀ u, HasMinCostChain G S (augCost G c b bν) u ] ∧
      ∀ (r : Fin n → ℝ) (S : Finset (Fin n)) (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ),
        IsSinkSelection G S → (∃ x, IsFlow G r x) →
        (∀ p ∈ G.A, ¬ SameComponent G p.1 p.2 →
          b p.1 p.2 * (∑ i, max (r i) 0) ≤ c p.1 p.2 (∑ i, max (r i) 0)) →
        (((∃ (r' : Fin n → ℝ) (x : Fin n → Fin n → ℝ), IsMinCostFlow G c r' x) ↔
            ∃ π : Fin n → ℝ, ∀ p ∈ G.A, ∀ x, IsFlow G r x →
              0 ≤ reducedArcCost c π p.1 p.2 (x p.1 p.2)) ∧
          ((∃ (r' : Fin n → ℝ) (x : Fin n → Fin n → ℝ), IsMinCostFlow G c r' x) →
            (∀ i, minChainCost G S (augCost G c b bν) i ≠ ⊥ ∧
              minChainCost G S (augCost G c b bν) i ≠ ⊤) ∧
            ∀ p ∈ G.A, ∀ x, IsFlow G r x →
              0 ≤ reducedArcCost c (fun i => (minChainCost G S (augCost G c b bν) i).toReal)
                p.1 p.2 (x p.1 p.2))) := by sorry

end SendSplit.Existence
