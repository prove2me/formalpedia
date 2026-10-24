-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P30_symmetricPureState_delta
-- name    : QAlgorithms.Papers.Independent.Support50.P30.symmetricPureState_delta
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:28:00.012295+00:00
-- url     : https://prove2.me/theorems/c4adeae4-5730-4406-b655-7ae4f43f45af
-- title:
--   Unnumbered trainability statistic for symmetric pure states
-- statement:
--   Let $n\ge1$ and let $\psi$ be a normalized pure state invariant under every qubit permutation. In any fixed orthonormal Schur coordinates, its density matrix $\rho=|\psi\rangle\langle\psi|$ is supported in the symmetric sector $\lambda=(n,0)$, of dimension $n+1$ and multiplicity one. Its centered statistic is
--
--   $$\Delta(\rho_{(n,0)})=1-\frac1{n+1},\qquad \frac12\le\Delta(\rho_{(n,0)})\le1.$$
--
--   This gives a state-independent $\Theta(1)$ data statistic. It does not by itself guarantee a nonzero derivative in every generator and measurement direction.
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, PDF p. 29, Unnumbered trainability statistic for symmetric pure states

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.29, Example 1's single-state identity, with a uniform Theta(1)
bound. No conclusion of nonzero gradients in every direction is asserted. -/
theorem symmetricPureState_delta {n : ℕ} (hn : 1 ≤ n) (S : SchurFrame n)
    (psi : EuclideanSpace ℂ (Qubits n)) (hpsi : IsState psi)
    (hsym : ∀ p : Equiv.Perm (Fin n), act (qubitPermutationMatrix n p) psi = psi) :
    centeredDelta (aggregate S (symmetricSector n) (pureDensity psi)) = 1 - 1 / ((n : ℝ) + 1) ∧
    (1 / 2 : ℝ) ≤ centeredDelta (aggregate S (symmetricSector n) (pureDensity psi)) ∧
    centeredDelta (aggregate S (symmetricSector n) (pureDensity psi)) ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end
