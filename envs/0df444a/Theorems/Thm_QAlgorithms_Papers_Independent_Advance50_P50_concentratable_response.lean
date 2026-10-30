-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_concentratable_response
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.concentratable_response
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:19:09.029785+00:00
-- url     : https://prove2.me/theorems/74f15eaf-acd8-4e42-a0d3-7c143e8f508b
-- title:
--   Eq.(37): concentratable entanglement response
-- statement:
--   An $n$-qubit input $\rho$ is a positive semidefinite, trace-one matrix on the fixed computational basis, of dimension $d=2^n$. A $k$-copy model has a fixed input-independent unitary $U$, a Hermitian observable $O$, effective observable $\widetilde O=U^\dagger O U$, and exact response $h(\rho)=\operatorname{Tr}[U\rho^{\otimes k}U^\dagger O]$. Let $\rho=|\psi\rangle\langle\psi|$ be a pure $n$-qubit density matrix with $\|\psi\|=1$, and let $\rho_Q=\operatorname{Tr}_{S\setminus Q}\rho$ for $S=\{1,\ldots,n\}$. For two copies, $S_Q$ swaps the copies at precisely the sites in $Q$ and acts as identity elsewhere. For any $Q\subseteq S$, let the effective observable be identity minus $2^{-|Q|}$ times the tensor product of $(I+\mathrm{SWAP})$ on each paired site in $Q$ and identity on the remaining sites. Then
--
--   $$h(\rho)=1-\frac1{2^{|Q|}}\sum_{A\subseteq Q}\operatorname{Tr}(\rho_A^2).$$
--
--   The empty subsystem reduction is the scalar trace one. Hence $Q=\varnothing$ gives zero, with a nonzero denominator. This is the purity formula associated with the concentratable-entanglement observable, without an added identification axiom.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 14, Eq.(37): concentratable entanglement response

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.14, Eq.(37): the tensor observable gives the subset-purity formula.
Q may be empty; then the response is zero. -/
theorem concentratable_response {n : ℕ} (Q : Finset (Fin n))
    (M : ExpectationModel (Qubits n) 2) (hobs : M.effective = concentratableObservable Q)
    (rho : Mat (Qubits n)) (hpure : IsPure rho) :
    M.response rho = 1 - ((2 : ℝ) ^ Q.card)⁻¹ *
      ∑ A ∈ Q.powerset, purity (subsystemReduction (fun _ => Bool) rho A) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
