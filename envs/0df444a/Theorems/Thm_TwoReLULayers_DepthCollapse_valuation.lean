-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_valuation
-- name    : TwoReLULayers.DepthCollapse.valuation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:11.225305+00:00
-- url     : https://prove2.me/theorems/e2f2db37-1750-4f53-a5a7-edb8711ce78c
-- title:
--   Lemma 15 — Valuation
-- statement:
--   Let $n\ge2$, let $A\subseteq E_n$ be an affine subspace, and let $P_1,\ldots,P_k\subseteq A$ be nonempty polytopes with arbitrary real coefficients $c_1,\ldots,c_k$. If their indicators satisfy $\sum_i c_i1_{P_i}=0$ pointwise on $A$, then
--   $$\sum_i c_i h_{P_i}(x)=0\qquad\text{for every }x\in E_n.$$
--   This full real valuation identity transfers indicator relations to global support-function identities; the conclusion is not restricted to $A$.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: support functions modulo lower affine dimension and almost everywhere on an affine space → the published supportFn, algebraic Submodule.span, integer dimension cutoffs and finite proper affine exceptional subspaces; reason: these express the source maximum, finite span and relative geometric convention exactly, including dimension zero
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 21, Lemma 15

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem valuation {n k : ℕ} (hn : 2 ≤ n) (A : AffineSubspace ℝ (E n))
    (P : Fin k → Set (E n)) (c : Fin k → ℝ)
    (hP : ∀ i, IsPolytope (P i) ∧ P i ⊆ A)
    (hcancel : ∀ y ∈ A, ∑ i, c i * indicator (P i) y = 0) :
    (fun x => ∑ i, c i * support (P i) x) = (0 : E n → ℝ) := by sorry

end TwoReLULayers.DepthCollapse
