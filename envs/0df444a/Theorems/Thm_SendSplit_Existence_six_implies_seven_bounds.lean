-- Prove2me | Theorems.Thm_SendSplit_Existence_six_implies_seven_bounds
-- name    : SendSplit.Existence.six_implies_seven_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:24:22.694945+00:00
-- url     : https://prove2.me/theorems/397eea1a-6833-4252-b049-154d8331bdf0
-- title:
--   Proof of Theorem 1, p. 639 — under 6°: $c_{ij}(x_{ij}) \ge \underline{c}_{ij}x_{ij}$ on flows and $\underline{\pi}_i - \underline{\pi}_j \le \underline{c}_{ij}$
-- statement:
--   Let $G$ be a graph with arc costs $c_{ij}$ concave on $[0,\infty)$ and $c_{ij}(0)=0$, let $r$ be a demand vector and $z = \sum_i r_i^+$. Let $S$ contain exactly one node of each sink strong component of $G$ and no other node, and let $\underline{c}$ be the arc costs of the augmented graph $\underline{G}$: $\dot c_{ij}(\infty)$ on arcs inside strong components, a real $b_{ij}$ on arcs of $G$ joining distinct strong components, a real $b^\nu_i$ on the appended arcs $(i,\nu)$. Assume
--
--   1. $b_{ij}\, z \le c_{ij}(z)$ for every arc $(i,j)$ joining distinct strong components, and
--   2. (condition 6°) from every node of $\underline{G}$ there is a minimum-cost chain to $\nu$ under $\underline{c}$.
--
--   Then $c_{ij}(x_{ij}) \ge \underline{c}_{ij}\,x_{ij}$ for every flow $x$ for $r$ and every arc $(i,j)$ of $G$; every minimum chain cost $\underline{\pi}_i$ is a real number; and
--
--   $$\underline{\pi}_i - \underline{\pi}_j \le \underline{c}_{ij} \qquad \text{for every arc } (i,j) \text{ of } G.$$
--
--   Together these give 7° with $\pi = \underline{\pi}$.
--
--   **Formalization Note** The products and the inequality $\underline{\pi}_i \le \underline{c}_{ij} + \underline{\pi}_j$ are stated in `EReal`, so that no `EReal` subtraction occurs; with $\underline{\pi}$ real this is the paper's inequality. The hypothesis 6° is assumed for the given $S$ and $\underline{c}$ only.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 639, proof of Theorem 1 (6° implies 7°)

import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_AugmentedGraph

namespace SendSplit.Existence

theorem six_implies_seven_bounds {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (r : Fin n → ℝ) (S : Finset (Fin n))
    (hS : IsSinkSelection G S) (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ)
    (hext : ∀ p ∈ G.A, ¬ SameComponent G p.1 p.2 →
      b p.1 p.2 * (∑ i, max (r i) 0) ≤ c p.1 p.2 (∑ i, max (r i) 0))
    (h6 : ∀ u, HasMinCostChain G S (augCost G c b bν) u) :
    (∀ x, IsFlow G r x → ∀ p ∈ G.A,
        augCost G c b bν (some p.1) (some p.2) * ((x p.1 p.2 : ℝ) : EReal)
          ≤ ((c p.1 p.2 (x p.1 p.2) : ℝ) : EReal)) ∧
      (∀ i, minChainCost G S (augCost G c b bν) i ≠ ⊥ ∧
        minChainCost G S (augCost G c b bν) i ≠ ⊤) ∧
      ∀ p ∈ G.A, minChainCost G S (augCost G c b bν) p.1
        ≤ augCost G c b bν (some p.1) (some p.2) + minChainCost G S (augCost G c b bν) p.2 := by sorry

end SendSplit.Existence
