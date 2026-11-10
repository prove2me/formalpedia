-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_polytope_coordinates
-- name    : TwoReLULayers.DepthCollapse.polytope_coordinates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:17.2645+00:00
-- url     : https://prove2.me/theorems/445513a8-cfac-46fa-b033-1001179c259e
-- title:
--   Affine-dimension reduction with field-preserving coordinates
-- statement:
--   Let $P\subseteq E_n$ be a nonempty polytope with vertices in a real subfield $R$, where $n\ge1$, and let $r=\dim P$. There are $p\in R^n$, a linear map $B:E_n\to E_r$ whose rows have coefficients in $R$, and a nonempty full-dimensional $R$-polytope $Q\subseteq E_r$ such that
--   $$h_P(x)=\langle p,x\rangle+h_Q(Bx)\quad\text{for every }x\in E_n.$$
--   This retains the translation term and reduces by affine dimension rather than number of vertices. Coordinates preserve $R$; no orthonormal basis introducing square roots is required. The case $r=0$ is included.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - generalization: the lower-dimensional remainder polytopes have dimension at most n-2 → field-preserving affine coordinate factorization for any nonempty polytope of affine dimension r; reason: finite affine-basis coordinates work in every affine dimension and specialize to all remainder polytopes
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 9, Section 1.3, lower-dimensional reduction, with Section 8, p. 24

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem polytope_coordinates {n r : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ)
    (P : Set (E n)) (hP : IsPolytopeOver R P) (hr : affineDim P = r) :
    ∃ p : E n, ∃ rows : Fin r → E n, ∃ Q : Set (E r),
      Over R p ∧ (∀ i, Over R (rows i)) ∧ IsPolytopeOver R Q ∧ affineDim Q = r ∧
      ∀ x : E n, support P x = dot p x +
        support Q (WithLp.toLp 2 (fun i => dot (rows i) x)) := by sorry

end TwoReLULayers.DepthCollapse
