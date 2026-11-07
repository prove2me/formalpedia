-- Prove2me | Theorems.Thm_PlantedSubgraphLD_lemma_4_2
-- name    : PlantedSubgraphLD.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:54.118117+00:00
-- url     : https://prove2.me/theorems/48f23723-709e-4a21-9a7e-befe7edaa2fa
-- title:
--   Lemma 4.2 — the restriction map $\Delta_F$ is injective, so $|\mathrm{Tri}(F)|\le\prod_i|\mathrm{Tri}(T_i)|$
-- statement:
--   Let $\Gamma$ be a finite simple graph and $F$ a nonempty abstract graph with $N_\Gamma(F)>0$. Let $\mathcal T(F)=(T_1,\dots,T_m)$ be an ordered edge decomposition of $F$, given by its piece types, and fix, for each copy $F^\circ\in C_\Gamma(F)$, an ordered edge decomposition $\mathcal T(F^\circ)=(T^\circ_1,\dots,T^\circ_m)$ compatible with it ($T^\circ_i\in C_\Gamma(T_i)$ for every $i$). Then the restriction map
--
--   $$
--   \Delta_F:\mathrm{Tri}(F)\to\mathrm{Tri}(T_1)\times\cdots\times\mathrm{Tri}(T_m)
--   $$
--
--   of (4.4) is injective. Consequently,
--
--   $$
--   |\mathrm{Tri}(F)|\le\prod_{i=1}^m|\mathrm{Tri}(T_i)| .
--   $$
--
--   Together with Lemma 4.1 this gives the product bound (4.5), $\beta_n(F)\le n^{\mathrm{ov}(F,\mathcal T(F))}\prod_i\beta_n(T_i)$.
--
--   Differences from the source:
--   - generalization: the planted graph Γn (a graph on at most n vertices, n large) → any finite simple graph Γ; reason: the statement is combinatorial in Γ; the paper's Γn is a special case
--   - encoding: abstract graphs F (isomorphism classes of graphs without isolated vertices) with NΓ(F) > 0, F nonempty → elements of AbsGraph Γ, the isomorphism classes of nonempty edge subsets of Γ; e(F), v(F), |Aut(F)|, connectedness read off the representative Quotient.out F; reason: the classes of nonempty subgraphs of Γ are exactly the nonempty abstract graphs with NΓ(F) > 0, and the invariants do not depend on the representative
--   - encoding: the i-th component (T°1,i, T°2,i, ψi) of ∆F, an element of Tri(Ti) → restrictTriple: the piece T°1,i and the restriction ψ|T°1,i as a map from V(T°1,i) into V; reason: T°2,i = ψi(T°1,i) is determined by the other two, so the record is injective exactly when ∆F is; building ∆F with values in Tri(Ti) would put isomorphism proofs into a definition
--   - encoding: a compatible decomposition: T°i ∈ CΓ(Ti) → spanned (dec S i) ≃g spanned (Quotient.out (τ i)): the piece is isomorphic to the representative of Ti; reason: a piece of a decomposition of a subgraph of Γ is a nonempty subgraph of Γ, so membership in CΓ(Ti) is exactly being isomorphic to Ti
--   - encoding: a fixed choice of one compatible decomposition for each copy → a function dec from the copies of F to tuples of edge sets, with every value an ordered edge decomposition compatible with the types τ; reason: the statement holds for every such choice, as on p.18
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), Lemma 4.2, §4.1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_restrictTriple
import Definitions.Def_PlantedSubgraphLD_ov

namespace PlantedSubgraphLD

/-- **Lemma 4.2.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.1, Lemma 4.2, p.18 (PDF p.20): "For every nonempty abstract graph
F with NΓn(F) > 0, the map ∆F defined in (4.4) is injective. Consequently, we have
|Tri(F)| ≤ ∏_{i=1}^{m} |Tri(Ti)|."

Here `T(F) = (T₁, …, T_m)` is a specified ordered edge decomposition of `F` (the types `τ`),
and `dec` fixes for every copy `F° ∈ C_Γ(F)` one compatible ordered edge decomposition
`T(F°)` (each piece `T°ᵢ` is a copy of `Tᵢ`), as on p.18.

**Formalization Note** The `i`-th component of `Δ_F` is recorded by `restrictTriple` as the
piece `T°₁,ᵢ` and the restriction `ψ|_{T°₁,ᵢ}` (into `V`); this record determines
`(T°₁,ᵢ, ψ(T°₁,ᵢ), ψ|_{T°₁,ᵢ})`, so its injectivity is that of `Δ_F`. Compatibility is
`T°ᵢ ≃ Tᵢ` (an isomorphism to the representative of `Tᵢ`). Stated for any finite simple graph
`Γ`. -/
theorem lemma_4_2 {V : Type} [Fintype V] [DecidableEq V] (Γ : SimpleGraph V) (F : AbsGraph Γ)
    (m : ℕ) (τ : Fin m → AbsGraph Γ) (dec : Copy Γ F → Fin m → Finset (Sym2 V))
    (hdec : ∀ S : Copy Γ F, IsOrderedEdgeDecomp S.1.1 (dec S))
    (hcompat : ∀ (S : Copy Γ F) (i : Fin m),
      Nonempty (spanned (dec S i) ≃g spanned (Quotient.out (τ i) : EdgeSub Γ).1)) :
    Function.Injective (fun t : Tri Γ F => fun i => restrictTriple dec t i) ∧
    Nat.card (Tri Γ F) ≤ ∏ i, Nat.card (Tri Γ (τ i)) := by sorry

end PlantedSubgraphLD
