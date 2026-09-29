-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_no_theta5_theta6_mesh
-- name    : RobertsonSeymour1986.GM5.no_theta5_theta6_mesh
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:02:08.624548+00:00
-- url     : https://prove2.me/theorems/6192d987-c38f-40ac-a176-6cfd88b59f43
-- title:
--   (5.3) A graph with no $\theta$-grid minor has no $(\theta_5,\theta_6)$-mesh
-- statement:
--   Let $\theta\ge 6$ be even and let $G$ be a finite graph with no $\theta$-grid minor. Then
--
--   $$G \text{ has no } (\theta_5,\theta_6)\text{-mesh},$$
--
--   that is, there are no disjoint connected subgraphs $A_1,\dots,A_{\theta_5}$ and disjoint connected subgraphs $B_1,\dots,B_{\theta_6}$ with every $A_i$ meeting every $B_j$. This is the explicit form of the paper's result (1.6), and it is the step of the main proof that uses the excluded grid.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (5.3), p. 102 (PDF p. 11); DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_NoGridMinor
import Definitions.Def_RobertsonSeymour1986_GM5_Params
import Definitions.Def_RobertsonSeymour1986_GM5_WebSpiderMesh

namespace RobertsonSeymour1986.GM5

/-- (5.3): a graph without a θ-grid minor has no `(θ₅, θ₆)`-mesh (the explicit form of (1.6)).

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (5.3), p. 102 (PDF p. 11): "If G ∈ 𝓕_θ then G has no (θ₅, θ₆)-mesh."

**Formalization Note** The standing assumption of p. 95 (PDF p. 4), "θ is a fixed even integer with θ ≥ 6", is the pair
of hypotheses `Even θ`, `6 ≤ θ`; "G ∈ 𝓕_θ" is `NoGridMinor θ G`. `θ₅, θ₆` are `theta5 θ`, `theta6 θ`. -/
theorem no_theta5_theta6_mesh {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (θ : ℕ) (hθe : Even θ) (hθ6 : 6 ≤ θ) (hG : NoGridMinor θ G) :
    ¬ ∃ (A : Fin (theta5 θ) → G.Subgraph) (B : Fin (theta6 θ) → G.Subgraph), IsMesh A B := by sorry

end RobertsonSeymour1986.GM5
