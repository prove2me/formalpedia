-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_valuation_mod_lower
-- name    : TwoReLULayers.DepthCollapse.valuation_mod_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:07.396912+00:00
-- url     : https://prove2.me/theorems/63aa0a63-5712-4231-a7ac-cacd7de60e54
-- title:
--   Corollary 16 — Valuation modulo lower affine dimension
-- statement:
--   Let $A\subseteq E_n$ be a nonempty $d$-dimensional affine space, where $n\ge2$, and let $P_i\subseteq A$ be nonempty polytopes with real coefficients $c_i$. If $\sum_i c_i1_{P_i}=0$ outside a finite union of proper affine subspaces of $A$, then
--   $$\sum_i c_i h_{P_i}\in\operatorname{span}_{\mathbb R}\{h_Q:Q\subseteq A\text{ nonempty polytope},\ \dim Q\le d-1\}.$$
--   In particular,
--   $$d\le n-1\quad\Longrightarrow\quad \sum_i c_i h_{P_i}\equiv0.$$
--   Both clauses are retained. At $d=0$ the generator set in the first clause is empty, so its span is the zero subspace.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: support functions modulo lower affine dimension and almost everywhere on an affine space → the published supportFn, algebraic Submodule.span, integer dimension cutoffs and finite proper affine exceptional subspaces; reason: these express the source maximum, finite span and relative geometric convention exactly, including dimension zero
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 21, Corollary 16

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem valuation_mod_lower {n k d : ℕ} (hn : 2 ≤ n)
    (A : AffineSubspace ℝ (E n)) (hA : (A : Set (E n)).Nonempty)
    (hd : Module.finrank ℝ A.direction = d)
    (P : Fin k → Set (E n)) (c : Fin k → ℝ)
    (hP : ∀ i, IsPolytope (P i) ∧ P i ⊆ A)
    (hcancel : GeomAE A (fun y => ∑ i, c i * indicator (P i) y = 0)) :
    (fun x => ∑ i, c i * support (P i) x) ∈ lowerSpanOn (A : Set (E n)) ((d : ℤ) - 1) ∧
    (d ≤ n - 1 → Congr (fun x => ∑ i, c i * support (P i) x) 0) := by sorry

end TwoReLULayers.DepthCollapse
