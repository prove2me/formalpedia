-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_polytopic_image_dimension
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.polytopic_image_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:12:45.265519+00:00
-- url     : https://prove2.me/theorems/201d56b6-6139-46ed-99cb-a75bf0f83ed4
-- title:
--   Affine dimension bound for a polytopic image
-- statement:
--   Let $d,n,k\ge1$ and let $T:M_d(\mathbb C)\to M_n(\mathbb C)$ be a quantum channel whose physical image is a polytope with exactly $k$ distinct vertices. Its real affine dimension satisfies
--   $$\dim_{\mathrm{aff},\mathbb R}\operatorname{Im}(T)\le k-1\le d-1.$$
--
--   Both inequalities constrain the size of polytopic images; the dimension is not a complex linear-span dimension.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 6, Corollary 3.6, Dimension of polytopic images

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

/-- Corollary 3.6, PDF p.6: real affine dimension ≤k−1≤d−1, with k,d positive. -/
theorem polytopic_image_dimension {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (T : Superop (Fin d) (Fin n)) (hT : IsChannel T) : DimensionGeometry T := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
