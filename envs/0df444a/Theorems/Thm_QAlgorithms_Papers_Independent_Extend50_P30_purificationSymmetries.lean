-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_purificationSymmetries
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.purificationSymmetries
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:28:16.109304+00:00
-- url     : https://prove2.me/theorems/60c19ec7-c5c2-484e-b097-e8561c742fa2
-- title:
--   Standard purification and real unitary symmetries
-- statement:
--   Let $\rho$ be any positive semidefinite matrix on a finite computational-basis space and $O$ any real unitary matrix. Define the standard, possibly unnormalized purification by row-first vectorization, $|\Psi\rangle=\sum_{ij}(\rho^{1/2})_{ij}|i,j\rangle$. No trace-one or invertibility assumption is made, and $\rho=0$ is allowed.
--
--   $$
--   (O\otimes O)|\Psi\rangle=|\Psi\rangle\iff\rho O=O\rho.
--   $$
--
--   This gives the source's standard purification and real unitary symmetries in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 57, lemma-7.5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

open scoped ComplexOrder in
/-- PDF p.57, Lemma 7.5: no trace normalization, so rho=0 is allowed; row-first vectorization. -/
theorem purificationSymmetries {I : Type*} [Fintype I] [DecidableEq I]
    (rho O : Matrix I I ℂ) (hrho : rho.PosSemidef)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (hreal : ∀ i j, (O i j).im = 0) :
    QAlgorithms.act (Matrix.kronecker O O) (rowVectorize (cfc Real.sqrt rho)) =
      rowVectorize (cfc Real.sqrt rho) ↔ rho * O = O * rho := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
