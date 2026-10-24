-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_adjoint_product_covariance
-- name    : QAlgorithms.Papers.Independent.Support50.P35.adjoint_product_covariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:41:35.630172+00:00
-- url     : https://prove2.me/theorems/e942f438-9450-46d1-bb75-6495c410a2f4
-- title:
--   Adjoint invariance and covariance of the coordinate products
-- statement:
--   Let \(D\geq1\), let \(\lambda_j\) be the norm-one traceless Gellmann matrices, and let \(a,b\in\mathbb R^{D^2-1}\). Define \(a\cdot b=\sum_ja_jb_j\), \((a\wedge b)_l=\sum_{jk}a_jb_k f_{jkl}\), and \((a\star b)_l=\sum_{jk}a_jb_k d_{jkl}\), using the antisymmetric and symmetric trace structure constants, respectively. For \(U\in SU(D)\), set \(O(U)_{jk}=\operatorname{tr}(\lambda_jU\lambda_kU^\dagger)\), a real number. Then
--
--   $$
--   O(U)a\cdot O(U)b=a\cdot b,\qquad
--   O(U)a\wedge O(U)b=O(U)(a\wedge b),\qquad
--   O(U)a\star O(U)b=O(U)(a\star b).
--   $$
--
--   Only traceless coordinates enter these products. This describes their transformation under the actual adjoint action.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 13, Unnumbered Eqs.(34)–(36): invariant dot, wedge and star products

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF p.13, Eqs.(34)--(36): all three covariance identities under SU(D).
No converse for arbitrary orthogonal matrices is asserted. -/
theorem adjoint_product_covariance (D : ℕ) (hD : 0 < D)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hdet : (U : Matrix (Fin D) (Fin D) ℂ).det = 1)
    (a b : TracelessIndex D → ℝ) :
    dotProduct (adjointAction U a) (adjointAction U b) = dotProduct a b ∧
    wedge (adjointAction U a) (adjointAction U b) = adjointAction U (wedge a b) ∧
    starProduct (adjointAction U a) (adjointAction U b) = adjointAction U (starProduct a b) := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
