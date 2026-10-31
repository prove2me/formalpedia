-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_vertex_fibre_span
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.vertex_fibre_span
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:11:16.783666+00:00
-- url     : https://prove2.me/theorems/8956a962-fdb5-4d08-8760-63b899591717
-- title:
--   Spans of pure preimages of a vertex
-- statement:
--   Let $T:M_d(\mathbb C)\to M_n(\mathbb C)$ be a quantum channel, with $d,n\ge1$, and let $\sigma$ be a vertex of its state image in the supporting-hyperplane sense. If $x_1,\ldots,x_k$ are unit vectors satisfying $T(x_ix_i^*)=\sigma$, then
--   $$T(xx^*)=\sigma\quad\text{for every unit }x\in\operatorname{span}_{\mathbb C}\{x_1,\ldots,x_k\}.$$
--   No independence or orthogonality is required of the given vectors. For an empty family its span has no unit vector.
--
--   Thus the span of pure preimages stays in the same pure-state fibre.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 5, Corollary 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P01

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P01

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Information100.P07 (projection)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

/-- Corollary 3.3, PDF p.5: the span of pure preimages of one vertex is again its fibre. -/
theorem vertex_fibre_span {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (T : Superop (Fin d) (Fin n)) (hT : IsChannel T) : FibreSpanGeometry T := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
