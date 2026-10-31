-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_geometry_linear_extension
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.geometry_linear_extension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:25:50.763239+00:00
-- url     : https://prove2.me/theorems/cf909d95-9d87-4514-93eb-f8722b0ec5a7
-- title:
--   The five geometric results for arbitrary complex-linear maps
-- statement:
--   Let $d,n\ge1$ and let $T:M_d(\mathbb C)\to M_n(\mathbb C)$ be any complex-linear map. Its input image remains the image of positive semidefinite trace-one matrices. Without any positivity or trace-preservation assumption, all five geometric conclusions of Section 3 hold: the two-pure-state restriction and distinct-vertex orthogonality of Lemma 3.2; the fibre-span conclusion of Corollary 3.3; the canonical orthogonal block decomposition of Proposition 3.4; both directions of Theorem 3.5, including residual-image containment and vertex exclusion; and, for an image polytope with $k\ge1$ vertices,
--   $$\dim_{\mathrm{aff},\mathbb R}\operatorname{Im}T\le k-1\le d-1.$$
--   Vertices use the supporting-hyperplane definition. Their output matrices are unrestricted matrices. The classical-quantum block formula here means the basis-measurement linear formula with arbitrary output matrices, not a CPTP predicate.
--
--   This gives the explicitly announced extension with precisely the same five paper-local geometric conclusions.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 3, §3 opening: geometry also holds for arbitrary linear matrix maps

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

/-- §3 opening, PDF p.3, and the five geometric results on PDF pp.4–6: explicitly
announced extension to arbitrary COMPLEX-LINEAR maps. Output matrices are unrestricted;
no complete positivity or trace preservation is reintroduced. -/
theorem geometry_linear_extension {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (T : Mat d →ₗ[ℂ] Mat n) :
    TwoPureGeometry T ∧ FibreSpanGeometry T ∧ VertexDecompositionGeometry T ∧
      PolytopeGeometry T ∧ DimensionGeometry T := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
