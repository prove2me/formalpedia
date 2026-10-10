-- Prove2me | Theorems.Thm_ShortestGCS_MICP_proof_5_7_path_and_cycles
-- name    : ShortestGCS.MICP.proof_5_7_path_and_cycles
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:09.745049+00:00
-- url     : https://prove2.me/theorems/2cbf74fb-0d1c-461f-bf61-04579135d13c
-- title:
--   Proof of Theorem 5.7, p. 10 — binary flows satisfying (5.5b)–(5.5d) form the vertex-disjoint union of an s-t path and cycles
-- statement:
--   Let $G$ be a directed graph with $s \ne t$, no edge entering $s$ and no edge leaving $t$. Let $y \in \{0,1\}^{\mathcal E}$ satisfy
--
--   $$
--   \sum_{e\in\mathcal E^{\mathrm{out}}_s} y_e = 1,\quad \sum_{e\in\mathcal E^{\mathrm{in}}_t} y_e = 1,\quad
--   \sum_{e\in\mathcal E^{\mathrm{in}}_v} y_e = \sum_{e\in\mathcal E^{\mathrm{out}}_v} y_e,\quad \sum_{e\in\mathcal E^{\mathrm{out}}_v} y_e \le 1 \quad (v \ne s,t),
--   $$
--
--   the flow parts of (5.5b)–(5.5d). Then there is an $s$-$t$ path $p$ such that:
--
--   1. every edge of $p$ has $y_e = 1$;
--   2. every other edge $e = (u,w)$ with $y_e = 1$ has both endpoints off $p$;
--   3. in the set $C$ of edges with $y_e = 1$ that are not on $p$, every vertex has as many incoming as outgoing edges, and at most one outgoing edge.
--
--   Thus $\{e : y_e = 1\}$ is the vertex-disjoint union of the path $p$ and the directed cycles formed by $C$.
--
--   **Formalization Note** Only the flow parts of the MICP constraints are assumed (the vector constraints of (5.5d) and (5.5e) are not needed), which makes the statement stronger than the page's "flows that satisfy the constraints in (5.5)". The assumption $|\mathcal E^{\mathrm{in}}_s| = |\mathcal E^{\mathrm{out}}_t| = 0$ is that of p. 7. A self-loop with unit flow counts as a cycle of length one. The cycle condition is stated through in- and out-degrees in $C$.
-- source:
--   Marcucci, Umenberger, Parrilo & Tedrake, Shortest Paths in Graphs of Convex Sets, arXiv:2101.11565v5, proof of Theorem 5.7, p. 10, first sentence

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun
import Definitions.Def_ShortestGCS_MICP_Setting

namespace ShortestGCS.MICP

/-- Proof of Theorem 5.7, arXiv:2101.11565v5, p. 10, first sentence: binary flows satisfying the
flow parts of (5.5b)–(5.5d) describe the vertex-disjoint union of an `s`-`t` path and cycles.
Concretely there is an `s`-`t` path `p` all of whose edges carry flow `1`; every other edge with
flow `1` avoids the vertices of `p`; and on those other edges every vertex has equal in- and
out-degree, at most `1` (so they form vertex-disjoint directed cycles). Uses the assumption
`|ℰ_s^in| = |ℰ_t^out| = 0` of p. 7. -/
theorem proof_5_7_path_and_cycles {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n)
    (hst : NoInSNoOutT G) (hne : G.s ≠ G.t) (y : V × V → ℝ)
    (hbin : ∀ e ∈ G.E, y e = 0 ∨ y e = 1)
    (hsource : ∑ e ∈ outEdges G G.s, y e = 1) (htarget : ∑ e ∈ inEdges G G.t, y e = 1)
    (hdeg : ∀ v, v ≠ G.s → v ≠ G.t → ∑ e ∈ outEdges G v, y e ≤ 1)
    (hcons : ∀ v, v ≠ G.s → v ≠ G.t → ∑ e ∈ inEdges G v, y e = ∑ e ∈ outEdges G v, y e) :
    ∃ p : List V, IsPath G p ∧ (∀ e ∈ pathEdges p, y e = 1) ∧
      (∀ e ∈ G.E, y e = 1 → e ∉ pathEdges p → e.1 ∉ p ∧ e.2 ∉ p) ∧
      ∀ v : V,
        (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.2 = v).card =
            (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.1 = v).card ∧
          (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.1 = v).card ≤ 1 := by sorry

end ShortestGCS.MICP
