-- Prove2me | Theorems.Thm_PoAIndep_Topology_cost_eq_sum_edges
-- name    : PoAIndep.Topology.cost_eq_sum_edges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:14.535075+00:00
-- url     : https://prove2.me/theorems/b0e1665e-2478-43e5-8925-d05b839861d8
-- title:
--   §2.1, p. 5 — the cost of a flow is the edge sum C(f) = Σₑ ℓₑ(fₑ)fₑ
-- statement:
--   Let $(G,r,\ell)$ be an instance and let $f$ be a flow, that is, a nonnegative assignment of flow to simple source–sink paths of each commodity. The cost of $f$ is defined as the total latency $C(f)=\sum_{P}\ell_P(f)f_P$, summed over all commodities and paths. Summing over the edges of each path and reversing the order of summation gives the edge form
--   $$C(f)=\sum_{e\in E}\ell_e(f_e)\,f_e .$$
--
--   The edge form is how the cost enters every later argument of the paper: Lemmas 3.5 and 3.7 and Theorem 3.8 all compare flows edge by edge.
--
--   **Formalization Note.** Neither feasibility nor any property of the latency functions is needed. The identity uses that a simple path contains each edge at most once.
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 5, §2.1, third paragraph

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

namespace PoAIndep.Topology

theorem cost_eq_sum_edges {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I) (hf : IsFlow I f) :
    cost I f = ∑ e, I.ℓ e (edgeFlow I f e) * edgeFlow I f e := by sorry

end PoAIndep.Topology
