-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_general_density_convex_hull
-- name    : QAlgorithms.Papers.Independent.Support50.P35.general_density_convex_hull
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:46:05.688616+00:00
-- url     : https://prove2.me/theorems/67398e2b-cef2-44fd-b818-98d48ccea078
-- title:
--   Density hull in an arbitrary operator basis
-- statement:
--   Let \(D>0\), and let \(\mu_\alpha\), \(1\leq\alpha\leq D^2\), be a complete Hermitian orthonormal basis. Reconstruct \(\rho(c)=\sum_\alpha c_\alpha\mu_\alpha\). Let \(V_\mu\) be the real quadratic locus defined by trace one, \(\sum_\alpha c_\alpha^2=1\), and \(\sum_{\alpha\beta}c_\alpha c_\beta\operatorname{Re}\operatorname{tr}(\mu_\alpha\mu_\beta\mu_\gamma)=c_\gamma\) for every \(\gamma\). Then
--
--   $$
--   \{c:\rho(c)\succeq0,\ \operatorname{tr}\rho(c)=1\}=\operatorname{conv}V_\mu.
--   $$
--
--   All density matrices, including pure boundary matrices, occur on the left. This is the general-basis version of the source's state-space hull assertion.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 16, Unnumbered p.16: density hull in a general operator basis

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF p.16: general operator-basis density hull, including its pure boundary.
The source's rank-D means operators on a D-dimensional space here. -/
theorem general_density_convex_hull (D : ℕ) (hD : 0 < D)
    (mu : Fin (D ^ 2) → Matrix (Fin D) (Fin D) ℂ)
    (hmu : IsHermitianONBasis mu) :
    {c : Fin (D ^ 2) → ℝ | IsDensityMatrix (hermitianReconstruction mu c)} =
      convexHull ℝ (generalPureSet mu) := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
