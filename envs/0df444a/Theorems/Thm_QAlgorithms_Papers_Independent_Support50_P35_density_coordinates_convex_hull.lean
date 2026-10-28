-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_density_coordinates_convex_hull
-- name    : QAlgorithms.Papers.Independent.Support50.P35.density_coordinates_convex_hull
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:43:19.137825+00:00
-- url     : https://prove2.me/theorems/15e6e650-1347-4f4b-b313-59173512af0e
-- title:
--   The density-coordinate set is the pure-state convex hull
-- statement:
--   For \(D\geq1\), reconstruct \(\rho(c)=(I+\sum_jc_j\lambda_j)/D\) in the paper's norm-one traceless Gellmann basis. Let \(\mathcal P_\star\) be the quadratic locus \(c\cdot c=D(D-1)\), \(c\star c=(D-2)c\). Then
--
--   $$
--   \{c:\rho(c)\succeq0,\ \operatorname{tr}\rho(c)=1\}=\operatorname{conv}\mathcal P_\star.
--   $$
--
--   The hull uses finite convex combinations. The density set includes pure boundary points; “rank-D” is read as operators on a \(D\)-dimensional space. This supplies the convex domain for the roof construction.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 14, Unnumbered p.14: all density coordinates form the convex hull of pure coordinates

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF p.14: the density-coordinate set is the finite convex hull of the
pure quadratic variety; pure boundary states are included among densities. -/
theorem density_coordinates_convex_hull (D : ℕ) (hD : 0 < D) :
    {c : TracelessIndex D → ℝ | IsDensityMatrix (scaledGellmannState c)} =
      convexHull ℝ (pureQuadraticSet D) := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
