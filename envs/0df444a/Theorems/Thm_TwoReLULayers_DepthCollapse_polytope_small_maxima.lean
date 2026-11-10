-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_polytope_small_maxima
-- name    : TwoReLULayers.DepthCollapse.polytope_small_maxima
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:24.460138+00:00
-- url     : https://prove2.me/theorems/9b0817fa-3624-4aac-b855-53931331aee2
-- title:
--   Lower-dimensional support functions have small-arity maxima
-- statement:
--   Let $P\subseteq E_n$ be a nonempty polytope over a real subfield $R$, where $n\ge1$, and let $r=\dim P$. Then there are finitely many signs $\sigma_i\in\{-1,1\}$ and $R$-linear maps $A_i:E_n\to E_{r+1}$ such that
--   $$h_P(x)=\sum_i\sigma_i\operatorname{MAX}_{r+1}(A_i x)\quad\text{for every }x\in E_n.$$
--   The affine maps in the formal representation have zero biases. This states the small-arity reduction needed for the lower-dimensional remainder, including translated polytopes and the point case $r=0$. A polytope may have arbitrarily many vertices; no vertex-count bound is assumed.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - generalization: support functions of remainder polytopes of dimension at most n-2 reduce to maxima of arity at most n-1 → an r-dimensional polytope over any real subfield has a signed homogeneous MAX_(r+1) representation for every r; reason: the affine-dimension reduction and Eq. (2) apply in every dimension; r ≤ n-2 recovers the source claim
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 9, Section 1.3, lower-dimensional remainder discussion, using Eq. (2), p. 2

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem polytope_small_maxima {n r : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ)
    (P : Set (E n)) (hP : IsPolytopeOver R P) (hr : affineDim P = r) :
    ∃ k : ℕ, ∃ σ : Fin k → ℝ, ∃ A : Fin k → AffineR R n (r + 1),
      (∀ i, IsSign (σ i)) ∧ (∀ i j, (A i j).bias = 0) ∧
      ∀ x : E n, support P x = ∑ i, σ i * maxCoord (affineEval (A i) x) := by sorry

end TwoReLULayers.DepthCollapse
