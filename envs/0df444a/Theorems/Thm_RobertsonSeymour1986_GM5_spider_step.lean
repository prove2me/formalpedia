-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_spider_step
-- name    : RobertsonSeymour1986.GM5.spider_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:59:42.862981+00:00
-- url     : https://prove2.me/theorems/0a8ba5d7-39d7-4774-8499-5c23f82495c7
-- title:
--   (4.5) From a $(\phi_k,\psi_k)$-web with $k$ spiders to a $(\phi_{k+1},\psi_{k+1})$-web with $k+1$ spiders
-- statement:
--   Let $\theta\ge 6$ be even and let $G$ be a finite graph with no $\theta$-grid minor. Let $0\le k<\theta_1$. If $G$ has a $(\phi_k,\psi_k)$-web with $k$ pairwise edge-disjoint spiders, then $G$ has a $(\phi_{k+1},\psi_{k+1})$-web with $k+1$ pairwise edge-disjoint spiders.
--
--   Here $\phi_k,\psi_k,\theta_1$ are the parameters of Sections 2 and 4, and the spiders are spiders of the web they accompany. Starting from a $(\theta_2,\theta_2)$-web ($\theta_2=\psi_0\ge\phi_0$, so it contains a $(\phi_0,\psi_0)$-web), $\theta_1$ applications give a web with $\theta_1$ edge-disjoint spiders, which (4.2) forbids.
--
--   **Formalization Note** The printed statement reads "For $0\le k<\theta_2$". This is a misprint for $\theta_1$: $\phi_{k+1}$ and $\psi_{k+1}$ are defined only for $k+1\le\theta_1$, and the proof of (4.6) uses the lemma exactly for $k<\theta_1$.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (4.5), p. 99 (PDF p. 8), with the printed range "0 ≤ k < θ₂" read as "0 ≤ k < θ₁"; DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_NoGridMinor
import Definitions.Def_RobertsonSeymour1986_GM5_Params
import Definitions.Def_RobertsonSeymour1986_GM5_WebSpiderMesh

namespace RobertsonSeymour1986.GM5

/-- (4.5): one more edge-disjoint spider at the price of shrinking the web from `(φ_k, ψ_k)` to
`(φ_{k+1}, ψ_{k+1})`.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (4.5), p. 99 (PDF p. 8): "For 0 ≤ k < θ₂, if G ∈ 𝓕_θ has a (φ_k, ψ_k)-web with k
edge-disjoint spiders, then it has a (φ_{k+1}, ψ_{k+1})-web with k + 1 edge-disjoint spiders."

**Formalization Note** The printed range "0 ≤ k < θ₂" is a misprint for "0 ≤ k < θ₁": φ_{k+1} and
ψ_{k+1} are defined only for `k + 1 ≤ θ₁` (Sect. 2 and p. 99), and (4.6) applies (4.5) exactly for
`k < θ₁`. The statement uses `k < θ₁`. The standing assumption of p. 95 (PDF p. 4), "θ is a fixed even integer with θ ≥ 6", is the pair
of hypotheses `Even θ`, `6 ≤ θ`; "G ∈ 𝓕_θ" is `NoGridMinor θ G`. The spiders `C l` are spiders of the web named
in the same clause and are pairwise edge-disjoint. -/
theorem spider_step {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (θ : ℕ) (hθe : Even θ) (hθ6 : 6 ≤ θ) (hG : NoGridMinor θ G)
    (k : ℕ) (hk : k < theta1 θ)
    (h : ∃ (A : Fin (phi θ k) → G.Subgraph) (B : Fin (psi θ k) → G.Subgraph)
        (C : Fin k → G.Subgraph),
        IsWeb A B ∧ (∀ l, IsSpider A B (C l)) ∧
        Pairwise (fun l l' => Disjoint (C l).edgeSet (C l').edgeSet)) :
    ∃ (A : Fin (phi θ (k + 1)) → G.Subgraph) (B : Fin (psi θ (k + 1)) → G.Subgraph)
        (C : Fin (k + 1) → G.Subgraph),
        IsWeb A B ∧ (∀ l, IsSpider A B (C l)) ∧
        Pairwise (fun l l' => Disjoint (C l).edgeSet (C l').edgeSet) := by sorry

end RobertsonSeymour1986.GM5
