-- Prove2me | Theorems.Thm_ShortestGCS_MICP_remark_5_5
-- name    : ShortestGCS.MICP.remark_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:14:18.702266+00:00
-- url     : https://prove2.me/theorems/672b3b70-54a2-4779-8bdd-96a66af0416c
-- title:
--   Remark 5.5, p. 9 — a valid equality Σ_{e∈ℰ_v} c_e y_e + d = 0 for (5.2) gives the valid equality Σ_in c_e z′_e + Σ_out c_e z_e + d x_v = 0
-- statement:
--   Let $G$ be a graph of convex sets satisfying the standing assumptions of §2, $v$ a vertex with no self-loop $(v,v)$, and $c_e, d \in \mathbb R$. If the constraint (5.3) holds with equality at every feasible point of the biconvex program (5.2),
--
--   $$
--   \sum_{e\in\mathcal E_v} c_e y_e + d = 0,
--   $$
--
--   then the linear equality
--
--   $$
--   \sum_{e\in\mathcal E^{\mathrm{in}}_v} c_e z'_e + \sum_{e\in\mathcal E^{\mathrm{out}}_v} c_e z_e + d\, x_v = 0
--   $$
--
--   holds at every feasible point of (5.2).
--
--   Applied to the flow conservation of the LP (5.1), this gives the vector part of the constraint (5.5d) of the MICP.
--
--   **Formalization Note** As in Lemma 5.4, the hypothesis $(v,v)\notin\mathcal E$ is a disclosed addition that the page's partition of $\mathcal E_v$ presupposes.
-- source:
--   Marcucci, Umenberger, Parrilo & Tedrake, Shortest Paths in Graphs of Convex Sets, arXiv:2101.11565v5, Remark 5.5, p. 9

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun
import Definitions.Def_ShortestGCS_MICP_Setting

namespace ShortestGCS.MICP

/-- Remark 5.5, arXiv:2101.11565v5, p. 9: if the valid constraint (5.3) holds with equality at every
feasible point of (5.2), then `∑_{e ∈ ℰ_v^in} c_e z'_e + ∑_{e ∈ ℰ_v^out} c_e z_e + d x_v = 0` is a valid
linear equality for (5.2). Disclosed addition: `(v, v) ∉ ℰ`, as in Lemma 5.4. -/
theorem remark_5_5 {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n) (hG : IsGCS G)
    (v : V) (hloop : (v, v) ∉ G.E) (c : V × V → ℝ) (d : ℝ)
    (hvalid : ∀ (y : V × V → ℝ) (x : V → Fin n → ℝ) (z z' : V × V → Fin n → ℝ),
      IsFeasible52 G y x z z' → ∑ e ∈ edgesAt G v, c e * y e + d = 0) :
    ∀ (y : V × V → ℝ) (x : V → Fin n → ℝ) (z z' : V × V → Fin n → ℝ),
      IsFeasible52 G y x z z' →
        ∑ e ∈ inEdges G v, c e • z' e + ∑ e ∈ outEdges G v, c e • z e + d • x v = 0 := by sorry

end ShortestGCS.MICP
