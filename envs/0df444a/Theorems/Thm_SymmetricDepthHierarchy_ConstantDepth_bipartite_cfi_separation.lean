-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_bipartite_cfi_separation
-- name    : SymmetricDepthHierarchy.ConstantDepth.bipartite_cfi_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:46.517734+00:00
-- url     : https://prove2.me/theorems/cbc8786a-04b0-4f12-bd52-edc5f70963ed
-- title:
--   Lemma B.22 (corrected: nontrivial $G$): bipartite CFI graphs $B(\widehat G_i)$ agree on $\mathcal C$ and separate graphs with a $G$ minor
-- statement:
--   Let $\mathcal C$ be a minor-closed graph class and $G$ a connected graph with at least two vertices such that no graph in $\mathcal C$ admits a weak oddomorphism to $G$. Let $B_i:=B(\widehat G_i)$ for $i\in\{0,1\}$. Then
--
--   1. $B_0$ and $B_1$ are simple bipartite graphs with $\gamma(G)$ vertices on either side;
--   2. $\mathrm{hom}_{\mathrm{bip}}(F',B_0)=\mathrm{hom}_{\mathrm{bip}}(F',B_1)$ for all bipartite $F'\in\mathcal C$ with any fixed bipartition;
--   3. $\mathrm{hom}_{\mathrm{bip}}(F,B_0)>\mathrm{hom}_{\mathrm{bip}}(F,B_1)$ for every bipartite graph $F$ with fixed bipartition that contains $G$ as a minor.
--
--   These host graphs, of size $\gamma(G)$ per side, witness Theorem 3.7.
--
--   Differences from the source:
--   - correction: G connected (any number of vertices) → G connected with |V(G)| ≥ 2; reason: counterexample: C = ∅ (minor-closed, vacuously no weak oddomorphism) and G = K₁: the empty incidence assignment has parity 0, so G₀ has one vertex and G₁ none; Ĝᵢ adds no edges; B₀ has one vertex per side and B₁ none, contradicting clause 1 for any value of γ(K₁). In Theorem 3.7 the condition follows from K₁ ∈ 𝓕, minor-closedness and G ∉ 𝓕
--   - encoding: G_1: the CFI graph G_W for W of odd total weight (well defined up to isomorphism) → G_1 := G_W with W = indicator of an arbitrary vertex v₀ (statement for every v₀); reason: up to isomorphism G_W depends only on ∑ W [Rob26, Cor. 3.7]; every choice of v₀ is one representative
--   - encoding: B(H) with sides V(H) × {0} and V(H) × {1} → BipGraph with both sides V(H); (u,0) ~ (v,1) iff u = v or uv ∈ E(H); reason: the second coordinate only records the side
--   - encoding: a class of simple graphs → a set of FinGraph (finite vertex type in Type with a simple graph); reason: classes here are minor-closed or defined by an isomorphism-invariant predicate, so membership does not depend on the encoding
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 38 (PDF p. 41), Lemma B.22

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Pattern
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Oddomorphism
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_CFI

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Lemma B.22 (corrected: nontrivial `G`), printed p. 38 (PDF p. 41). Let `𝓒` be a minor-closed
graph class and `G` a connected graph with at least two vertices such that no graph in `𝓒` admits a
weak oddomorphism to `G`. Let `Bᵢ := B(Ĝᵢ)` for `i ∈ {0, 1}` (`Ĝ₁` built from the odd twist at an
arbitrary vertex `v₀`). Then
1. `B₀` and `B₁` are simple bipartite graphs with `γ(G)` vertices on either side,
2. `hom_bip(F', B₀) = hom_bip(F', B₁)` for all bipartite `F' ∈ 𝓒` with any fixed bipartition, and
3. `hom_bip(F, B₀) > hom_bip(F, B₁)` for every bipartite graph `F` with fixed bipartition that
   contains `G` as a minor. -/
theorem bipartite_cfi_separation (𝓒 : GraphClass) (h𝓒 : MinorClosed 𝓒) {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (hG : G.Connected) (hV : 2 ≤ Fintype.card V)
    (hno : ∀ Y ∈ 𝓒, ∀ φ : Y.G →g G, ¬ IsWeakOddomorphism φ) (v₀ : V) :
    (Fintype.card (BipGraph.lift (cfiHat G twist0)).L = cfiSize G ∧
      Fintype.card (BipGraph.lift (cfiHat G twist0)).R = cfiSize G ∧
      Fintype.card (BipGraph.lift (cfiHat G (twist1 v₀))).L = cfiSize G ∧
      Fintype.card (BipGraph.lift (cfiHat G (twist1 v₀))).R = cfiSize G) ∧
    (∀ F' : BipGraph, (⟨F'.L ⊕ F'.R, F'.graph⟩ : FinGraph) ∈ 𝓒 →
      BipGraph.hombip F' (BipGraph.lift (cfiHat G twist0)) =
        BipGraph.hombip F' (BipGraph.lift (cfiHat G (twist1 v₀)))) ∧
    (∀ F : BipGraph, HadwigerConj.IsMinor G F.graph →
      BipGraph.hombip F (BipGraph.lift (cfiHat G (twist1 v₀))) <
        BipGraph.hombip F (BipGraph.lift (cfiHat G twist0))) := by sorry

end SymmetricDepthHierarchy.ConstantDepth
