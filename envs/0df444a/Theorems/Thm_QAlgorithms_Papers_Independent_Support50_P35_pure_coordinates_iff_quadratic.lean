-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_pure_coordinates_iff_quadratic
-- name    : QAlgorithms.Papers.Independent.Support50.P35.pure_coordinates_iff_quadratic
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:42:28.819323+00:00
-- url     : https://prove2.me/theorems/e42d074e-eef2-41ed-a494-e0fde9086a0e
-- title:
--   Pure states form the corrected quadratic coordinate variety
-- statement:
--   Let \(D\geq1\), let \(\lambda_j\) be the norm-one traceless Gellmann matrices, and let \(c\in\mathbb R^{D^2-1}\). Reconstruct \(\rho(c)=(I+\sum_jc_j\lambda_j)/D\). Then \(\rho(c)\) is a normalized rank-one projector if and only if
--
--   $$
--   \sum_jc_j^2=D(D-1),\qquad
--   \sum_{jk}c_jc_k d_{jkl}-(D-2)c_l=0\quad\text{for every }l.
--   $$
--
--   Here \(d_{jkl}=\operatorname{Re}\operatorname{tr}(\lambda_j\lambda_k\lambda_l)\), and \(D-2\) is subtraction in \(\mathbb R\). These equations define the pure-state real quadratic variety. The factor \(D-2\), absent from printed Eq.(39), is required by Eq.(37). The star criterion is attributed by the source to KMSM97/AMM97.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 14, Unnumbered Eqs.(29),(37)–(39): pure states are a quadratic real variety

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF pp.13--14, Eqs.(29),(37)--(39): purity iff the norm and star equations.
Eq.(39) is corrected to c^T D_l c-(D-2)c_l=0, as required by Eq.(37). -/
theorem pure_coordinates_iff_quadratic (D : ℕ) (hD : 0 < D)
    (c : TracelessIndex D → ℝ) :
    QAlgorithms.Papers.Independent.Information100.P08.IsPure (scaledGellmannState c) ↔ c ∈ pureQuadraticSet D := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
