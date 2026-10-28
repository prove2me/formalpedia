-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_general_basis_purity
-- name    : QAlgorithms.Papers.Independent.Support50.P35.general_basis_purity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:44:44.462709+00:00
-- url     : https://prove2.me/theorems/bce4f96e-a74b-46e9-96c9-a5590625a10f
-- title:
--   Purity equations in an arbitrary Hermitian orthonormal basis
-- statement:
--   Let \(D>0\), and let \(\mu_\alpha\), \(1\leq\alpha\leq D^2\), be any complete real orthonormal basis of Hermitian \(D\times D\) matrices for \(\operatorname{tr}(AB)\). Put \(\tau_\alpha=\operatorname{tr}\mu_\alpha\) and \(\chi_{\alpha\beta\gamma}=\operatorname{tr}(\mu_\alpha\mu_\beta\mu_\gamma)\), which may be complex. Then \(\mu_\alpha\mu_\beta=\sum_\gamma\chi_{\alpha\beta\gamma}\mu_\gamma\), and \(\rho(c)=\sum_\alpha c_\alpha\mu_\alpha\) for real \(c\) is a normalized rank-one projector if and only if
--
--   $$
--   \sum_\alpha c_\alpha\tau_\alpha=1,\qquad
--   \sum_\alpha c_\alpha^2=1,\qquad
--   \sum_{\alpha\beta}c_\alpha c_\beta\operatorname{Re}\chi_{\alpha\beta\gamma}=c_\gamma\quad(\text{all }\gamma).
--   $$
--
--   The imaginary contraction cancels because its indices are antisymmetric. Positivity is a consequence of these equations, not an additional premise. They exhibit the pure-coordinate set as a real quadratic variety.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 15, Unnumbered Eqs.(42)–(45): purity in any Hermitian orthonormal basis

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF p.15, Eqs.(42)--(45): no independent positivity hypothesis is added;
the equations imply a normalized rank-one projector. Complex chi is retained. -/
theorem general_basis_purity (D : ℕ) (hD : 0 < D)
    (mu : Fin (D ^ 2) → Matrix (Fin D) (Fin D) ℂ)
    (hmu : IsHermitianONBasis mu) :
    (∀ a b, mu a * mu b =
      ∑ g, multiplicationCoefficient mu a b g • mu g) ∧
    (∀ c : Fin (D ^ 2) → ℝ,
      QAlgorithms.Papers.Independent.Information100.P08.IsPure (hermitianReconstruction mu c) ↔ generalPureEquations mu c) := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
