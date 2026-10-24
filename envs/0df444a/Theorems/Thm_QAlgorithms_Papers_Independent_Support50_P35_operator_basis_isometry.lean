-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_operator_basis_isometry
-- name    : QAlgorithms.Papers.Independent.Support50.P35.operator_basis_isometry
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:45:28.710988+00:00
-- url     : https://prove2.me/theorems/1c1bca61-bb06-4abf-b440-53f9091363c2
-- title:
--   Operator-basis changes give inverse isometries of purity varieties
-- statement:
--   Let \(D>0\), and let \(\mu\) and \(\nu\) be two complete Hermitian orthonormal bases of \(D\times D\) matrices, with unscaled reconstruction \(R_\mu(c)=\sum_\alpha c_\alpha\mu_\alpha\). Define \(O_{\beta\alpha}=\operatorname{tr}(\mu_\alpha\nu_\beta)\). Then
--
--   $$
--   O^TO=OO^T=I,\qquad O^{-1}=O^T=O_{\mu\leftarrow\nu},\qquad
--   R_\nu(Oc)=R_\mu(c),\qquad (Oc)\cdot(Od)=c\cdot d.
--   $$
--
--   Writing \(V_\mu\) and \(V_\nu\) for the trace-one, unit-norm, idempotency quadratic loci, one has \(c\in V_\mu\iff Oc\in V_\nu\) and \(d\in V_\nu\iff O^Td\in V_\mu\). Also \(O^TOc=c\) and \(OO^Td=d\). Thus the varieties are related by inverse linear isometries. The group is \(O(D^2)\); the source's unrestricted \(SO(D^2)\) claim is corrected because ordered bases can reverse orientation.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 15, Unnumbered Eqs.(46)–(49): operator-basis change is an isomorphism of varieties

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF pp.15--16, Eqs.(46)--(49): orthogonal isometry and inverse, with both
variety directions and reconstruction. The printed universal SO is corrected
 to O: unrestricted ordered Hermitian bases may reverse orientation. -/
theorem operator_basis_isometry (D : ℕ) (hD : 0 < D)
    (mu nu : Fin (D ^ 2) → Matrix (Fin D) (Fin D) ℂ)
    (hmu : IsHermitianONBasis mu) (hnu : IsHermitianONBasis nu) :
    let O := basisChange nu mu
    O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
    basisChange mu nu = O.transpose ∧
    (∀ c d : Fin (D ^ 2) → ℝ, dotProduct (O.mulVec c) (O.mulVec d) = dotProduct c d) ∧
    (∀ c : Fin (D ^ 2) → ℝ,
      hermitianReconstruction nu (O.mulVec c) = hermitianReconstruction mu c ∧
      O.transpose.mulVec (O.mulVec c) = c ∧
      (generalPureEquations mu c ↔ generalPureEquations nu (O.mulVec c))) ∧
    (∀ d : Fin (D ^ 2) → ℝ,
      O.mulVec (O.transpose.mulVec d) = d ∧
      (generalPureEquations nu d ↔ generalPureEquations mu (O.transpose.mulVec d))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
