-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_gellmann_basis_and_products
-- name    : QAlgorithms.Papers.Independent.Support50.P35.gellmann_basis_and_products
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:40:34.833992+00:00
-- url     : https://prove2.me/theorems/90d961a2-147b-40e9-ac65-abe321c30b33
-- title:
--   Normalized Gellmann basis and multiplication identities
-- statement:
--   Let \(D\geq1\). In the computational basis, take the diagonal matrices \(\Gamma_a=(\sum_{b<a}|b\rangle\langle b|-(a-1)|a\rangle\langle a|)/\sqrt{a(a-1)}\) for \(2\leq a\leq D\), and the off-diagonal matrices \((|a\rangle\langle b|+|b\rangle\langle a|)/\sqrt2\) and \(-i(|a\rangle\langle b|-|b\rangle\langle a|)/\sqrt2\) for \(a<b\). Denote this family of \(D^2-1\) traceless Hermitian matrices by \(\lambda_j\), and set \(\lambda_0=I/\sqrt D\). Then the complete family is a real basis for Hermitian \(D\times D\) matrices and
--
--   $$
--   \operatorname{tr}(\lambda_\alpha\lambda_\beta)=\delta_{\alpha\beta},\qquad
--   \lambda_j\lambda_k=\frac{\delta_{jk}}D I+\sum_l(d_{jkl}+if_{jkl})\lambda_l,\qquad
--   \{\lambda_j,\lambda_k\}=\frac{2\delta_{jk}}D I+2\sum_l d_{jkl}\lambda_l.
--   $$
--
--   Here \(d_{jkl}=\operatorname{Re}\operatorname{tr}(\lambda_j\lambda_k\lambda_l)\) is completely symmetric and \(f_{jkl}=\operatorname{Im}\operatorname{tr}(\lambda_j\lambda_k\lambda_l)\) is completely antisymmetric. Roman indices exclude zero; Greek indices include it. At \(D=1\), only \(\lambda_0=I\) remains. These identities fix the paper's normalization for all coordinate statements.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 12, Unnumbered Eqs.(18)–(24): normalized operator basis and product identities

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF pp.11--12, Eqs.(18)--(24): completeness, orthonormality, product and
anticommutator identities, and the full symmetry/antisymmetry conventions. -/
theorem gellmann_basis_and_products (D : ℕ) (hD : 0 < D) :
    Fintype.card (TracelessIndex D) = D ^ 2 - 1 ∧
    IsHermitianONBasis (gellmann D) ∧
    (∀ j : TracelessIndex D, (normOneGellmannGenerator j).trace = 0) ∧
    (∀ j k : TracelessIndex D,
      normOneGellmannGenerator j * normOneGellmannGenerator k =
        (if j = k then (D : ℂ)⁻¹ else 0) • (1 : Matrix (Fin D) (Fin D) ℂ) +
        ∑ l, ((symmetricConstant j k l : ℂ) + Complex.I * antisymmetricConstant j k l) • normOneGellmannGenerator l) ∧
    (∀ j k : TracelessIndex D,
      normOneGellmannGenerator j * normOneGellmannGenerator k + normOneGellmannGenerator k * normOneGellmannGenerator j =
        (if j = k then 2 / (D : ℂ) else 0) • (1 : Matrix (Fin D) (Fin D) ℂ) +
        ∑ l, ((2 * symmetricConstant j k l : ℝ) : ℂ) • normOneGellmannGenerator l) ∧
    (∀ j k l : TracelessIndex D,
      symmetricConstant j k l = symmetricConstant k j l ∧
      symmetricConstant j k l = symmetricConstant k l j ∧
      antisymmetricConstant j k l = -antisymmetricConstant k j l ∧
      antisymmetricConstant j k l = antisymmetricConstant k l j) := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
