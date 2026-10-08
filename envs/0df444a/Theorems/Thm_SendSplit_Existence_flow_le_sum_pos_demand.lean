-- Prove2me | Theorems.Thm_SendSplit_Existence_flow_le_sum_pos_demand
-- name    : SendSplit.Existence.flow_le_sum_pos_demand
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:24:27.93372+00:00
-- url     : https://prove2.me/theorems/77449f42-d29c-475f-b410-373f66192f0d
-- title:
--   Proof of Theorem 1, p. 639 — the flow in an arc joining distinct strong components is at most $z = \sum_i r_i^+$
-- statement:
--   Let $G$ be a graph, $r$ a demand vector and $x$ a flow for $r$. For every arc $(i,j)$ of $G$ joining distinct strong components,
--
--   $$x_{ij} \;\le\; z = \sum_i r_i^+, \qquad r_i^+ = \max(r_i, 0).$$
--
--   This bound is what makes the hypothesis $\underline{c}_{ij} z \le c_{ij}(z)$ of Theorem 1 enough to bound $c_{ij}(x_{ij})$ below by $\underline{c}_{ij} x_{ij}$ on such arcs.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 639, proof of Theorem 1

import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_AugmentedGraph

namespace SendSplit.Existence

theorem flow_le_sum_pos_demand {n : ℕ} (G : ArcGraph n) (r : Fin n → ℝ)
    (x : Fin n → Fin n → ℝ) (hx : IsFlow G r x) (p : Fin n × Fin n) (hp : p ∈ G.A)
    (hpC : ¬ SameComponent G p.1 p.2) :
    x p.1 p.2 ≤ ∑ i, max (r i) 0 := by sorry

end SendSplit.Existence
