-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_no_theta2_web
-- name    : RobertsonSeymour1986.GM5.no_theta2_web
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:00:13.099543+00:00
-- url     : https://prove2.me/theorems/33896c6a-fb79-482a-9f55-6cc94d16cf5f
-- title:
--   (4.6) A graph with no $\theta$-grid minor has no $(\theta_2,\theta_2)$-web
-- statement:
--   Let $\theta\ge 6$ be even and let $G$ be a finite graph with no $\theta$-grid minor. Then
--
--   $$G \text{ has no } (\theta_2,\theta_2)\text{-web},$$
--
--   where $\theta_2=\phi_0+2\phi_1+\dots+2\phi_{\theta_1-1}+\phi_{\theta_1}$ is the parameter of Section 2. With (5.2) this gives (5.3): large meshes force large grid minors.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (4.6), p. 100 (PDF p. 9); DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_NoGridMinor
import Definitions.Def_RobertsonSeymour1986_GM5_Params
import Definitions.Def_RobertsonSeymour1986_GM5_WebSpiderMesh

namespace RobertsonSeymour1986.GM5

/-- (4.6): a graph without a θ-grid minor has no `(θ₂, θ₂)`-web.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (4.6), p. 100 (PDF p. 9): "If G ∈ 𝓕_θ then G has no (θ₂, θ₂)-web."

**Formalization Note** The standing assumption of p. 95 (PDF p. 4), "θ is a fixed even integer with θ ≥ 6", is the pair
of hypotheses `Even θ`, `6 ≤ θ`; "G ∈ 𝓕_θ" is `NoGridMinor θ G`. `θ₂` is `theta2 θ`. -/
theorem no_theta2_web {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (θ : ℕ) (hθe : Even θ) (hθ6 : 6 ≤ θ) (hG : NoGridMinor θ G) :
    ¬ ∃ (A : Fin (theta2 θ) → G.Subgraph) (B : Fin (theta2 θ) → G.Subgraph), IsWeb A B := by sorry

end RobertsonSeymour1986.GM5
