-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_Supplement_lemma_17
-- name    : RamseyDisambig.Spherical.Supplement.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:25:19.172127+00:00
-- url     : https://prove2.me/theorems/ed8e9310-f295-4d42-82ac-7c82b144d8a2
-- title:
--   Lemma 17 — Localization in forests of copies
-- statement:
--   Let $F$ and $H$ be graphs and let $\mathcal F$ be a nonempty forest of copies of $F$ in $H$, with associated graph $\Gamma(\mathcal F)$. Then:
--
--   1. any two distinct members $Q,Q'$ of $\mathcal F$ intersect in at most one vertex, or in the two ends $\{u,v\}$ of an edge $uv$ of $H$;
--   2. every clique of $\Gamma(\mathcal F)$ is contained in a common member of $\mathcal F$;
--   3. if two distinct vertices $u,v$ have at least three common neighbours in $\Gamma(\mathcal F)$, then they occur in a common member of $\mathcal F$; moreover every common neighbour $w$ of $u$ and $v$ occurs together with both $u$ and $v$ in a member of $\mathcal F$;
--   4. if $u_1u_2u_3u_4$ is a 4-cycle in $\Gamma(\mathcal F)$ and $u_1u_3$, $u_2u_4$ are non-edges of $H$, then some member of $\mathcal F$ contains $u_1,u_2,u_3,u_4$.
--
--   In formulas, part 4 reads
--   $$u_1\sim u_2\sim u_3\sim u_4\sim u_1 \text{ in }\Gamma(\mathcal F),\ u_1u_3,u_2u_4\notin E(H)\ \Longrightarrow\ \exists Q\in\mathcal F:\ \{u_1,u_2,u_3,u_4\}\subseteq V(Q).$$
--
--   These localization properties reduce the local restrictions of the constructions of Theorems 3 and 5 to configurations inside a single copy.
--
--   **Formalization Note** $\Gamma(\mathcal F)$ is a graph on the whole vertex type of $H$ whose vertices outside $\bigcup_{Q}V(Q)$ are isolated, so part 2 quantifies over vertex sets inside that union.
--
--   Differences from the source:
--   - encoding: a forest of copies, ordered F₁, …, F_m → a Finset of H.Subgraph, each isomorphic to F, with an ordering σ : Fin m ≃ 𝓕 satisfying the overlap condition; reason: a family is a finite set of copies and the ordering is existential, as on p. 15
--   - encoding: graphs F and H → SimpleGraph on arbitrary vertex types; reason: the source imposes no finiteness on F or H; the forest itself is finite
--   - encoding: Γ(𝓕) defined for a nonempty forest on vertex set ⋃ V(Q) → hypothesis 𝓕.Nonempty; copyGraph on all of V with vertices outside the union isolated; cliques in b) range over subsets of the union; reason: Γ(𝓕) is only defined for nonempty forests (p. 16); vertices adjacent in Γ lie in the union, so a), c), d) are unaffected
--   - reading: two vertices u and v; a 4-cycle u₁u₂u₃u₄; at least three common neighbours → u ≠ v; four pairwise distinct vertices; three pairwise distinct vertices adjacent in Γ to both u and v; reason: the vertices of a cycle are distinct, and 'two vertices' names two different vertices
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Lemma 17, p. 16 (proof pp. 16–17); forest of copies p. 15; Γ(𝓕) p. 16 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Supplement_ForestOfCopies

set_option autoImplicit false

namespace RamseyDisambig.Spherical.Supplement

/-- Lemma 17 (Localization in forests of copies), p. 16 (proof pp. 16–17), all four parts.
`Γ` is `copyGraph 𝓕`; the forest is nonempty, as required for `Γ(𝓕)` to be defined (p. 16). -/
theorem lemma_17 {V W : Type*} (F : SimpleGraph W) (H : SimpleGraph V)
    (𝓕 : Finset H.Subgraph) (h𝓕 : IsForestOfCopies F H 𝓕) (hne : 𝓕.Nonempty) :
    -- a) two distinct members meet in at most one vertex or in the two ends of an edge of H
    (∀ Q ∈ 𝓕, ∀ Q' ∈ 𝓕, Q ≠ Q' →
      (Q.verts ∩ Q'.verts).Subsingleton ∨
        ∃ u v : V, H.Adj u v ∧ Q.verts ∩ Q'.verts = {u, v}) ∧
    -- b) every clique of Γ(𝓕) lies in a common member
    (∀ s : Set V, s ⊆ copyUnion 𝓕 → (copyGraph 𝓕).IsClique s →
      ∃ Q ∈ 𝓕, s ⊆ Q.verts) ∧
    -- c) three common neighbours force a common member, which also holds each common neighbour
    (∀ u v : V, u ≠ v →
      (∃ w₁ w₂ w₃ : V, w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃ ∧
        (copyGraph 𝓕).Adj u w₁ ∧ (copyGraph 𝓕).Adj v w₁ ∧
        (copyGraph 𝓕).Adj u w₂ ∧ (copyGraph 𝓕).Adj v w₂ ∧
        (copyGraph 𝓕).Adj u w₃ ∧ (copyGraph 𝓕).Adj v w₃) →
      (∃ Q ∈ 𝓕, u ∈ Q.verts ∧ v ∈ Q.verts) ∧
      ∀ w : V, (copyGraph 𝓕).Adj u w → (copyGraph 𝓕).Adj v w →
        ∃ Q ∈ 𝓕, u ∈ Q.verts ∧ v ∈ Q.verts ∧ w ∈ Q.verts) ∧
    -- d) a 4-cycle u₁u₂u₃u₄ of Γ(𝓕) whose diagonals are non-edges of H lies in a member
    (∀ u₁ u₂ u₃ u₄ : V, u₁ ≠ u₂ → u₁ ≠ u₃ → u₁ ≠ u₄ → u₂ ≠ u₃ → u₂ ≠ u₄ → u₃ ≠ u₄ →
      (copyGraph 𝓕).Adj u₁ u₂ → (copyGraph 𝓕).Adj u₂ u₃ → (copyGraph 𝓕).Adj u₃ u₄ →
      (copyGraph 𝓕).Adj u₄ u₁ → ¬ H.Adj u₁ u₃ → ¬ H.Adj u₂ u₄ →
      ∃ Q ∈ 𝓕, u₁ ∈ Q.verts ∧ u₂ ∈ Q.verts ∧ u₃ ∈ Q.verts ∧ u₄ ∈ Q.verts) := by sorry

end RamseyDisambig.Spherical.Supplement
