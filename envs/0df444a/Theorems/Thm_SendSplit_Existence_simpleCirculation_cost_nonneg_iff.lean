-- Prove2me | Theorems.Thm_SendSplit_Existence_simpleCirculation_cost_nonneg_iff
-- name    : SendSplit.Existence.simpleCirculation_cost_nonneg_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:24:09.480471+00:00
-- url     : https://prove2.me/theorems/2c7f9aac-5b8b-4cd6-bcc4-c94e1862a654
-- title:
--   Proof of Theorem 1, p. 639 — $c(\theta y) \ge 0$ for all $\theta \ge 0$ iff $\sum_{(i,j)\in C}\dot c_{ij}(\infty) \ge 0$
-- statement:
--   Let $G$ be a graph with arc costs $c_{ij}$ concave on $[0,\infty)$ and $c_{ij}(0) = 0$, and let $y$ be a simple circulation whose induced subgraph is the simple circuit with arc set $C$. Then
--
--   $$c(\theta y) \ge 0 \ \text{ for all } \theta \ge 0 \quad\Longleftrightarrow\quad \sum_{(i,j)\in C} \dot c_{ij}(\infty) \ge 0,$$
--
--   where the right-hand sum is taken in $[-\infty, \infty)$.
--
--   This is the circuit-by-circuit form of the equivalence of 4° and 5° in Theorem 1.
--
--   **Formalization Note** $\dot c_{ij}(\infty)$ is `slopeAtInfty (c i j)` (see the AugmentedGraph definition), an `EReal`; the sum is an `EReal` sum of values that are never $+\infty$.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 639, proof of Theorem 1

import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_AugmentedGraph

namespace SendSplit.Existence

theorem simpleCirculation_cost_nonneg_iff {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (y : Fin n → Fin n → ℝ) (hy : IsSimpleCirculation G y) :
    (∀ θ : ℝ, 0 ≤ θ → 0 ≤ flowCost G c (fun i j => θ * y i j)) ↔
      0 ≤ ∑ p ∈ support G y, slopeAtInfty (c p.1 p.2) := by sorry

end SendSplit.Existence
