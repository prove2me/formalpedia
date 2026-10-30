-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_subsystem_impurity
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.subsystem_impurity
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:18:22.968076+00:00
-- url     : https://prove2.me/theorems/dafc1128-0dc4-438c-9c44-f40f030d8162
-- title:
--   Eq.(36): subsystem concurrence quantity
-- statement:
--   An $n$-qubit input $\rho$ is a positive semidefinite, trace-one matrix on the fixed computational basis, of dimension $d=2^n$. A $k$-copy model has a fixed input-independent unitary $U$, a Hermitian observable $O$, effective observable $\widetilde O=U^\dagger O U$, and exact response $h(\rho)=\operatorname{Tr}[U\rho^{\otimes k}U^\dagger O]$. Let $\rho=|\psi\rangle\langle\psi|$ be a pure $n$-qubit density matrix with $\|\psi\|=1$, and let $\rho_Q=\operatorname{Tr}_{S\setminus Q}\rho$ for $S=\{1,\ldots,n\}$. For two copies, $S_Q$ swaps the copies at precisely the sites in $Q$ and acts as identity elsewhere. For any nonempty $Q\subseteq S$, a two-copy model with $\widetilde O=2(I-S_Q)$ satisfies
--
--   $$h(\rho)=2\bigl(1-\operatorname{Tr}(\rho_Q^2)\bigr).$$
--
--   This preserves the displayed squared-concurrence quantity without taking a square root or asserting equality to an uninspected normalization. The full subsystem $Q=S$ is allowed, giving zero for pure $\rho$.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 14, Eq.(36): subsystem concurrence quantity

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

/-- PDF p.14, Eq.(36): the displayed squared-concurrence quantity, without
identifying it with a square root or a differently normalized cited measure.
Printed: PDF p.14 Eq.(36) writes a tensor product over j in Q of SWAP^(j) tensor the complementary identity.
Changed: Use the single original two-copy register: swap exactly the sites in Q and act as identity on its complement. The response is 2*(1-Tr(rho_Q^2)); no named-measure or square-root equivalence is asserted.
Why: The text introduces this as the subsystem version of Eq.(34). Literal repetition of full-register complementary identities would change the Hilbert-space dimension. The physical site embedding is the dimension-consistent reading of that formula. -/
theorem subsystem_impurity {n : ℕ} (Q : Finset (Fin n)) (hQ : Q.Nonempty)
    (M : ExpectationModel (Qubits n) 2)
    (hobs : M.effective = (2 : ℂ) • (1 - subsystemSwap Q))
    (rho : Mat (Qubits n)) (hpure : IsPure rho) :
    M.response rho = 2 * (1 - purity (subsystemReduction (fun _ => Bool) rho Q)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
