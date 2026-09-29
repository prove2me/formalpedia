-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_treewidth_le_theta9
-- name    : RobertsonSeymour1986.GM5.treewidth_le_theta9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:06:02.195192+00:00
-- url     : https://prove2.me/theorems/df9fba1d-40b0-4554-8c1e-50dec1ebf60a
-- title:
--   (7.3) A graph with no $\theta$-grid minor has tree-width at most $\theta_9$
-- statement:
--   Let $\theta\ge 6$ be even and let $G$ be a finite graph with no minor isomorphic to the $\theta$-grid. Then
--
--   $$\operatorname{tw}(G)\le\theta_9,$$
--
--   where $\theta_9=\theta_7(\theta_8+1)+1$ is the parameter of Section 2. The paper calls this its principal theorem. The main theorem (2.1) follows by taking $\theta=\theta(H)$.
--
--   **Formalization Note** "Tree-width at most $\theta_9$" means that $G$ has a tree-decomposition all of whose bags have at most $\theta_9+1$ vertices.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (7.3), p. 108 (PDF p. 17); DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_NoGridMinor
import Definitions.Def_RobertsonSeymour1986_GM5_Params
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

namespace RobertsonSeymour1986.GM5

/-- (7.3), "the principal theorem of this paper": a graph without a θ-grid minor has tree-width at
most `θ₉`.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (7.3), p. 108 (PDF p. 17): "If G ∈ 𝓕_θ then G has tree-width at most θ₉."

**Formalization Note** The standing assumption of p. 95 (PDF p. 4), "θ is a fixed even integer with θ ≥ 6", is the pair
of hypotheses `Even θ`, `6 ≤ θ`; "G ∈ 𝓕_θ" is `NoGridMinor θ G`. "Tree-width at most `θ₉`" is `TreewidthLE G (theta9 θ)`: some
tree-decomposition has all bags of size `≤ θ₉ + 1`. -/
theorem treewidth_le_theta9 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (θ : ℕ) (hθe : Even θ) (hθ6 : 6 ≤ θ) (hG : NoGridMinor θ G) :
    TreewidthLE G (theta9 θ) := by sorry

end RobertsonSeymour1986.GM5
