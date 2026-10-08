-- Prove2me | Theorems.Thm_SendSplit_Existence_hirsch_hoffman_extension
-- name    : SendSplit.Existence.hirsch_hoffman_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:12:37.778087+00:00
-- url     : https://prove2.me/theorems/f254b014-5b8c-4347-b789-a6a7df972c6c
-- title:
--   §2, p. 638 — extension of Hirsch–Hoffman: c attains its minimum on the flows iff it is bounded below on each extreme ray; then at an extreme flow
-- statement:
--   Let $G$ be a graph with arc costs $c_{ij}$ concave on $[0,\infty)$ and $c_{ij}(0) = 0$, and let $r$ be a demand vector for which the set of flows is nonempty. Then the flow cost $c$ attains its minimum on the set of flows for $r$ if and only if, for every extreme flow $x$ for $r$ and every simple circulation $y$, the function
--
--   $$\theta \mapsto c(x + \theta y), \qquad \theta \ge 0,$$
--
--   is bounded below. Moreover, if a minimum-cost flow for $r$ exists, then some extreme flow is a minimum-cost flow for $r$.
--
--   The extreme flows are the extreme points and the simple circulations the extreme directions of recession of the polyhedron of flows, so this is the extension of the Hirsch–Hoffman theorem on concave minimization over polyhedra that the paper invokes. It is the step that turns 4° into 1° and 3°.
--
--   **Formalization Note** "Bounded below on each half-line" is the explicit statement $\exists M\ \forall \theta \ge 0,\ M \le c(x + \theta y)$; "assumes its minimum" is the existence of a minimum-cost flow.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 638, Section 2 (citing Hirsch–Hoffman 1961 and Rockafellar 1970, pp. 61, 343)

import Mathlib
import Definitions.Def_SendSplit_Existence_Network

namespace SendSplit.Existence

theorem hirsch_hoffman_extension {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (r : Fin n → ℝ) (hflow : ∃ x, IsFlow G r x) :
    ((∃ x, IsMinCostFlow G c r x) ↔
      ∀ x, IsExtremeFlow G r x → ∀ y, IsSimpleCirculation G y →
        ∃ M : ℝ, ∀ θ : ℝ, 0 ≤ θ → M ≤ flowCost G c (fun i j => x i j + θ * y i j)) ∧
    ((∃ x, IsMinCostFlow G c r x) → ∃ x, IsMinCostFlow G c r x ∧ IsExtremeFlow G r x) := by sorry

end SendSplit.Existence
