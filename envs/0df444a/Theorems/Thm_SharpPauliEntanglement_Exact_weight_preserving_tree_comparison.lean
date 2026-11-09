-- Prove2me | Theorems.Thm_SharpPauliEntanglement_Exact_weight_preserving_tree_comparison
-- name    : SharpPauliEntanglement.Exact.weight_preserving_tree_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:58:46.741568+00:00
-- url     : https://prove2.me/theorems/61dcc99c-30b1-4650-83af-16c104e6bfaa
-- title:
--   Lemma 3.6 — Endpoint/red-component bijections, weighted sum comparison, finiteness and degree bounds
-- statement:
--   Let $G$ be any finite simple graph, let $A\subseteq G$ mark its red edges, fix a root $v$, and use the weight parameters for $\Delta\ge2$. Form the simple-path tree $T_v$ of (3.22), rooted at $(v)$, with inherited edge colors and endpoint map $\pi$. Every connected $\gamma\ni v$ has a connected lift $\widehat\gamma$ containing the root such that $\pi$ bijects $\widehat\gamma$ onto $\gamma$ and maps its red components bijectively onto those of $A[\gamma]$. In particular, with the parameters of (2.5), for every $u\ge0$,
--
--   $$\sum_{\substack{\gamma\ni v\\G[\gamma]\text{ connected}}}u^{|\gamma|}w_A(\gamma)\le\sum_{\substack{U\ni(v)\\T_v[U]\text{ connected}}}u^{|U|}w_{\mathrm{red}}^{T_v}(U).$$
--
--   The tree is finite. Its root has $\deg_G(v)$ children and every other vertex has at most $\Delta-1$ children when $G$ has degree at most $\Delta$. All endpoint, component, tree, finiteness, and degree claims belong to the conclusion; none is a hypothesis supplied by an arbitrary covering object. This comparison is the combinatorial support for the colored connected-sum estimate.
--
--   Differences from the source:
--   - encoding: finite simple-path tree with vertices given in (3.22) → the explicitly enumerated finite carrier of distinct-vertex rooted path lists, with a graph restricted to that carrier; reason: lists encode exactly the source paths and the endpoint default is never used on the nonempty carrier
--   - encoding: edge colors and parameters from the section → a spanning subgraph A <= G, Delta >= 2, and a conditional degree bound only for the nonroot child count; reason: blue means an edge of G outside A; the comparison holds for every graph and the last degree assertion retains its source condition
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), printed/PDF p. 14, Lemma 3.6

import Definitions.Def_SharpPauliEntanglement_Exact_PathTree

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- Kiani, p. 14, Lemma 3.6, including the endpoint and red-component bijections,
comparison of sums, actual path-tree property, finiteness, and both child bounds. -/
theorem weight_preserving_tree_comparison {m : ℕ} (G A : SimpleGraph (Fin m))
    (hred : A ≤ G) (v : Fin m) (Δ : ℕ) (hΔ : 2 ≤ Δ) :
    (∀ γ : Finset (Fin m), v ∈ γ → ConnectedSet G γ →
      ∃ lift : Finset (List (Fin m)), lift ⊆ simplePaths G v ∧ [v] ∈ lift ∧
        ConnectedSet (pathTree G v) lift ∧
        Set.BijOn (pathEndpoint v) (lift : Set (List (Fin m))) (γ : Set (Fin m)) ∧
        PreservesRedComponents G A v lift γ) ∧
    (∀ u : ℝ, 0 ≤ u →
      connectedSum G A Δ Finset.univ v u ≤
        connectedSum (pathTree G v) (redPathTree G A v) Δ (simplePaths G v) [v] u) ∧
    (simplePaths G v : Set (List (Fin m))).Finite ∧
    ((pathTree G v).induce (simplePaths G v : Set (List (Fin m)))).IsTree ∧
    (pathChildren G v [v]).card = degree G v ∧
    (DegreeBound G Δ → ∀ p ∈ simplePaths G v, p ≠ [v] →
      (pathChildren G v p).card ≤ Δ - 1) := by sorry

end SharpPauliEntanglement.Exact
