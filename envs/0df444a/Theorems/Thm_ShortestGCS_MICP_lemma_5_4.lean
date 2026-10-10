-- Prove2me | Theorems.Thm_ShortestGCS_MICP_lemma_5_4
-- name    : ShortestGCS.MICP.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:56.825587+00:00
-- url     : https://prove2.me/theorems/6accaecb-b758-4019-abef-7877d1dba03e
-- title:
--   Lemma 5.4, p. 9 — a valid inequality Σ_{e∈ℰ_v} c_e y_e + d ≥ 0 for (5.2) lifts to the valid perspective constraint (5.4)
-- statement:
--   Let $G$ be a graph of convex sets satisfying the standing assumptions of §2, $v$ a vertex with no self-loop $(v,v)$, and $c_e \in \mathbb R$ ($e \in \mathcal E$), $d \in \mathbb R$. Suppose the linear inequality
--
--   $$
--   \sum_{e\in\mathcal E_v} c_e y_e + d \ge 0 \tag{5.3}
--   $$
--
--   is **valid** for the biconvex program (5.2), i.e. it holds at every feasible point of (5.2). Then the convex constraint
--
--   $$
--   \Big( \sum_{e\in\mathcal E^{\mathrm{in}}_v} c_e z'_e + \sum_{e\in\mathcal E^{\mathrm{out}}_v} c_e z_e + d\, x_v,\ \sum_{e\in\mathcal E_v} c_e y_e + d \Big) \in \tilde{\mathcal X}_v \tag{5.4}
--   $$
--
--   is also valid for (5.2): it holds at every feasible point $(y, x, z, z')$ of (5.2).
--
--   This lemma is the construction principle of the MICP: applied to the nonnegativity constraints $y_e \ge 0$ of the LP (5.1) it produces the perspective constraints (5.5e).
--
--   **Formalization Note** Disclosed addition: $(v,v) \notin \mathcal E$. The page partitions $\mathcal E_v$ into incoming and outgoing edges, which presupposes that no edge is both; a self-loop at $v$ would be counted once in (5.3) and twice in the first component of (5.4), and the lemma would fail. Validity is the paper's notion (a hypothesis and a conclusion over all feasible points of (5.2)).
-- source:
--   Marcucci, Umenberger, Parrilo & Tedrake, Shortest Paths in Graphs of Convex Sets, arXiv:2101.11565v5, Lemma 5.4, p. 9 (with the definition of ℰ_v and of a valid constraint, p. 9)

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun
import Definitions.Def_ShortestGCS_MICP_Setting

namespace ShortestGCS.MICP

/-- Lemma 5.4, arXiv:2101.11565v5, p. 9: if the linear inequality
`∑_{e ∈ ℰ_v} c_e y_e + d ≥ 0` (5.3) is valid for (5.2), i.e. holds at every feasible point of (5.2),
then the convex constraint (5.4)
`(∑_{e ∈ ℰ_v^in} c_e z'_e + ∑_{e ∈ ℰ_v^out} c_e z_e + d x_v, ∑_{e ∈ ℰ_v} c_e y_e + d) ∈ 𝒳̃_v`
is also valid for (5.2). Disclosed addition: `(v, v) ∉ ℰ` (the page's partition of `ℰ_v` into
incoming and outgoing edges presupposes that no edge is both). -/
theorem lemma_5_4 {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n) (hG : IsGCS G)
    (v : V) (hloop : (v, v) ∉ G.E) (c : V × V → ℝ) (d : ℝ)
    (hvalid : ∀ (y : V × V → ℝ) (x : V → Fin n → ℝ) (z z' : V × V → Fin n → ℝ),
      IsFeasible52 G y x z z' → 0 ≤ ∑ e ∈ edgesAt G v, c e * y e + d) :
    ∀ (y : V × V → ℝ) (x : V → Fin n → ℝ) (z z' : V × V → Fin n → ℝ),
      IsFeasible52 G y x z z' →
        (∑ e ∈ inEdges G v, c e • z' e + ∑ e ∈ outEdges G v, c e • z e + d • x v,
          ∑ e ∈ edgesAt G v, c e * y e + d) ∈ perspectiveSet (G.X v) := by sorry

end ShortestGCS.MICP
