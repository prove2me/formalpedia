-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_row_representative_calculus
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.row_representative_calculus
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-14T05:01:45.46259+00:00
-- url     : https://prove2.me/theorems/f35ca303-2467-43e2-8023-a8ac552c2098
-- title:
--   Row-vectorized superoperators: action, composition, and left-right multiplication
-- statement:
--   Fix a finite dimension $n$ and stack matrix entries in row order. For a complex-linear map $\Phi:M_n(\mathbb C)\to M_n(\mathbb C)$, let $M_\Phi$ be its matrix in the fixed matrix-unit basis. For any such maps $\Phi,\Psi$ and any matrices $A,B,X$,
--
--   $$\operatorname{vec}(\Phi(X))=M_\Phi\operatorname{vec}(X),\qquad M_{\Phi\circ\Psi}=M_\Phi M_\Psi,\qquad M_{X\mapsto AXB}=A\otimes B^{\mathsf T}.$$
--
--   These compatible identities translate quantum-channel covariance and composition into ordinary matrix algebra. They also hold for the empty zero-dimensional matrix space.
-- source:
--   Mozrzymas, Studzinski and Datta, Structure of irreducibly covariant quantum channels for finite groups, https://arxiv.org/abs/1610.05657v2, PDF pp.5–7, Eqs.(7)–(15), and Appendix A p.34; row-coordinate action and composition calculus underlying Lemma 9.

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31 QAlgorithms.Papers.Independent.Information100.P44 QAlgorithms.Papers.Independent.Dependency50.P16
open scoped Matrix ComplexConjugate
set_option autoImplicit false

theorem QAlgorithms.Papers.Independent.Extend50.P31.row_representative_calculus (n : ℕ) :
    (∀ (Phi : EndMat n) (X : Mat n), rowVec (Phi X) =
      (rowMatrixRepresentative Phi).mulVec (rowVec X)) ∧
    (∀ Phi Psi : EndMat n, rowMatrixRepresentative (Phi.comp Psi) =
      rowMatrixRepresentative Phi * rowMatrixRepresentative Psi) ∧
    (∀ A B : Mat n, rowMatrixRepresentative (sandwich A B) = Matrix.kronecker A Bᵀ) := by sorry
