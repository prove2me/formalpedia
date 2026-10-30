-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_global_impurity
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.global_impurity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:17:37.966089+00:00
-- url     : https://prove2.me/theorems/28c4f461-5e19-42f0-bd05-5dcaa99d4fd7
-- title:
--   Eq.(35): averaged single-site impurity
-- statement:
--   An $n$-qubit input $\rho$ is a positive semidefinite, trace-one matrix on the fixed computational basis, of dimension $d=2^n$. A $k$-copy model has a fixed input-independent unitary $U$, a Hermitian observable $O$, effective observable $\widetilde O=U^\dagger O U$, and exact response $h(\rho)=\operatorname{Tr}[U\rho^{\otimes k}U^\dagger O]$. Let $\rho=|\psi\rangle\langle\psi|$ be a pure $n$-qubit density matrix with $\|\psi\|=1$, and let $\rho_Q=\operatorname{Tr}_{S\setminus Q}\rho$ for $S=\{1,\ldots,n\}$. For two copies, $S_Q$ swaps the copies at precisely the sites in $Q$ and acts as identity elsewhere. Assume $n\ge1$ and $\widetilde O=(2/n)\sum_{j\in S}(I-S_{\{j\}})$. Then
--
--   $$h(\rho)=\frac2n\sum_{j\in S}\bigl(1-\operatorname{Tr}(\rho_{\{j\}}^2)\bigr).$$
--
--   This response is zero exactly when $\rho$ is fully product and strictly positive otherwise. It detects every nonproduct pure state, including states that factor across some nontrivial bipartition; no constant response on an arbitrary fixed-$E$ class is asserted.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 13, Eq.(35): averaged single-site impurity

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

/-- PDF pp.13–14, Eq.(35): averaged impurity, zero exactly on fully product
pure states and positive on every other pure state (including biseparable states). -/
theorem global_impurity {n : ℕ} (hn : 1 ≤ n) (M : ExpectationModel (Qubits n) 2)
    (hobs : M.effective = globalImpurityObservable n)
    (rho : Mat (Qubits n)) (hpure : IsPure rho) :
    M.response rho = (2 / (n : ℝ)) * ∑ j : Fin n, (1 - purity (subsystemReduction (fun _ => Bool) rho {j})) ∧
    (M.response rho = 0 ↔ FullyProduct rho) ∧
    (¬ FullyProduct rho → 0 < M.response rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
