-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_mesh_to_path_mesh
-- name    : RobertsonSeymour1986.GM5.mesh_to_path_mesh
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:01:27.45803+00:00
-- url     : https://prove2.me/theorems/43f379de-f7eb-4797-b21b-434be49acb6e
-- title:
--   (5.2) A large mesh contains a $(p,q)$-mesh whose first family consists of paths
-- statement:
--   Let $\theta\ge 6$ be even and let $G$ be a finite graph with no $\theta$-grid minor. Let $p,q\ge 2$ be integers and put
--
--   $$n=(\theta^2/2)^{q-1},\qquad m=p\binom{n}{q}+\tfrac12\theta^2\binom{n}{\theta^2/2}.$$
--
--   If $((A_1,\dots,A_m),(B_1,\dots,B_n))$ is an $(m,n)$-mesh in $G$, then there are $I\subseteq\{1,\dots,m\}$ and $J\subseteq\{1,\dots,n\}$ with $|I|=p$, $|J|=q$, and for each $i\in I$ a path $P_i$ contained in $A_i$, such that $((P_i : i\in I),(B_j : j\in J))$ is a $(p,q)$-mesh.
--
--   Applying the lemma twice, once to each side, turns a large mesh into a mesh made of paths. This is the step from meshes back to webs in (5.3).
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (5.2), p. 101 (PDF p. 10); DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_NoGridMinor
import Definitions.Def_RobertsonSeymour1986_GM5_IsPathSubgraph
import Definitions.Def_RobertsonSeymour1986_GM5_WebSpiderMesh

namespace RobertsonSeymour1986.GM5

/-- (5.2): a large mesh in a graph without a θ-grid minor contains a `(p, q)`-mesh whose first
family consists of paths inside the original subgraphs.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (5.2), p. 101 (PDF p. 10): "Let G ∈ 𝓕_θ, and let p, q ≥ 2 be integers. Let n = (θ²/2)^{q−1},
m = p\binom{n}{q} + ½θ²\binom{n}{θ²/2}. Suppose that ((A₁,…, A_m), (B₁,…, B_n)) is an (m, n)-mesh in
G. Then there exists I ⊆ {1,…, m} and J ⊆ {1,…, n} with |I| = p, |J| = q, and for each i ∈ I a path
P_i of A_i, such that ((P_i: i ∈ I), (B_j: j ∈ J)) is a (p, q)-mesh."

**Formalization Note** The standing assumption of p. 95 (PDF p. 4), "θ is a fixed even integer with θ ≥ 6", is the pair
of hypotheses `Even θ`, `6 ≤ θ`; "G ∈ 𝓕_θ" is `NoGridMinor θ G`. "½θ²" is `θ ^ 2 / 2` (exact for even `θ`); `q − 1` is exact since
`q ≥ 2`. "A path P_i of A_i" is a subgraph `P i ≤ A i` that is a path (`IsPathSubgraph`). -/
theorem mesh_to_path_mesh {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (θ : ℕ) (hθe : Even θ) (hθ6 : 6 ≤ θ) (hG : NoGridMinor θ G)
    (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (m n : ℕ) (hn : n = (θ ^ 2 / 2) ^ (q - 1))
    (hm : m = p * n.choose q + θ ^ 2 / 2 * n.choose (θ ^ 2 / 2))
    (A : Fin m → G.Subgraph) (B : Fin n → G.Subgraph) (hM : IsMesh A B) :
    ∃ (I : Finset (Fin m)) (J : Finset (Fin n)), I.card = p ∧ J.card = q ∧
      ∃ P : I → G.Subgraph, (∀ i, P i ≤ A i ∧ IsPathSubgraph (P i)) ∧
        IsMesh P (fun j : J => B j) := by sorry

end RobertsonSeymour1986.GM5
