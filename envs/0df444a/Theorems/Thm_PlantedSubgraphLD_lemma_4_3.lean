-- Prove2me | Theorems.Thm_PlantedSubgraphLD_lemma_4_3
-- name    : PlantedSubgraphLD.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:47.294533+00:00
-- url     : https://prove2.me/theorems/a991da92-d315-441d-8362-d2f59b625f0d
-- title:
--   Lemma 4.3 — the restriction maps combine to one injection on $\coprod_F\mathrm{Tri}(F)$
-- statement:
--   Let $\Gamma$ be a finite simple graph, let $\mathcal F$ be a collection of nonempty abstract graphs and fix $m\ge1$. For each $F\in\mathcal F$ specify an ordered edge decomposition $\mathcal T(F)=(T_1(F),\dots,T_m(F))$ and compatible decompositions of its concrete copies. Then the maps $\Delta_F$ combine to an injection
--
--   $$
--   \coprod_{F\in\mathcal F}\mathrm{Tri}(F)\longrightarrow\coprod_{(T_1,\dots,T_m)}\ \prod_{i=1}^m\mathrm{Tri}(T_i),\qquad (F,\tau)\mapsto\big(\mathcal T(F),\Delta_F(\tau)\big),
--   $$
--
--   where the disjoint union on the right is over the ordered tuples of piece types arising from the specified decompositions.
--
--   The injection is what allows the proof of Lemma 4.6 to sum the product bound over many abstract graphs at once without overcounting.
--
--   Differences from the source:
--   - generalization: the planted graph Γn (a graph on at most n vertices, n large) → any finite simple graph Γ; reason: the statement is combinatorial in Γ; the paper's Γn is a special case
--   - encoding: abstract graphs F (isomorphism classes of graphs without isolated vertices) with NΓ(F) > 0, F nonempty → elements of AbsGraph Γ, the isomorphism classes of nonempty edge subsets of Γ; e(F), v(F), |Aut(F)|, connectedness read off the representative Quotient.out F; reason: the classes of nonempty subgraphs of Γ are exactly the nonempty abstract graphs with NΓ(F) > 0, and the invariants do not depend on the representative
--   - encoding: the i-th component (T°1,i, T°2,i, ψi) of ∆F, an element of Tri(Ti) → restrictTriple: the piece T°1,i and the restriction ψ|T°1,i as a map from V(T°1,i) into V; reason: T°2,i = ψi(T°1,i) is determined by the other two, so the record is injective exactly when ∆F is; building ∆F with values in Tri(Ti) would put isomorphism proofs into a definition
--   - encoding: a compatible decomposition: T°i ∈ CΓ(Ti) → spanned (dec S i) ≃g spanned (Quotient.out (τ i)): the piece is isomorphic to the representative of Ti; reason: a piece of a decomposition of a subgraph of Γ is a nonempty subgraph of Γ, so membership in CΓ(Ti) is exactly being isomorphic to Ti
--   - encoding: 𝓕, a collection of nonempty abstract graphs → fam : Set (AbsGraph Γ), nonempty abstract graphs with NΓ(F) > 0; reason: Tri(F) is empty when NΓ(F) = 0, so such F add nothing to the domain and the injectivity statement is the same
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), Lemma 4.3, §4.1, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_restrictTriple
import Definitions.Def_PlantedSubgraphLD_ov

namespace PlantedSubgraphLD

/-- **Lemma 4.3.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.1, Lemma 4.3, p.19 (PDF p.21): "Let 𝓕 be a collection of nonempty
abstract graphs, and fix m ≥ 1. For each F ∈ 𝓕, specify an ordered edge decomposition
T(F) = (T1(F), . . . , Tm(F)) and compatible decompositions of its concrete copies. Then the maps
∆F combine to an injection ∐_{F∈𝓕} Tri(F) ⟶ ∐_{(T1,...,Tm)} ∏_{i=1}^{m} Tri(Ti), where the
disjoint union on the right is over the ordered tuples of piece types arising from the specified
decompositions."

**Formalization Note** The collection `fam` is a set of elements of `AbsGraph Γ` (abstract graphs
with `N_Γ(F) > 0`, the only ones with `Tri(F) ≠ ∅`). `τ F` is the specified decomposition
`T(F)`, `dec F` the compatible decompositions of the copies of `F`. An element of the right
side is recorded as the tuple of piece types together with the `restrictTriple` records of the
`m` component triples (see `lemma_4_2`). Stated for any finite simple graph `Γ`. -/
theorem lemma_4_3 {V : Type} [Fintype V] [DecidableEq V] (Γ : SimpleGraph V)
    (fam : Set (AbsGraph Γ)) (m : ℕ) (hm : 1 ≤ m) (τ : AbsGraph Γ → Fin m → AbsGraph Γ)
    (dec : (F : AbsGraph Γ) → Copy Γ F → Fin m → Finset (Sym2 V))
    (hdec : ∀ F ∈ fam, ∀ S : Copy Γ F, IsOrderedEdgeDecomp S.1.1 (dec F S))
    (hcompat : ∀ F ∈ fam, ∀ (S : Copy Γ F) (i : Fin m),
      Nonempty (spanned (dec F S i) ≃g spanned (Quotient.out (τ F i) : EdgeSub Γ).1)) :
    Function.Injective (fun x : (Σ F : fam, Tri Γ F.1) =>
      (τ x.1.1, fun i => restrictTriple (dec x.1.1) x.2 i)) := by sorry

end PlantedSubgraphLD
