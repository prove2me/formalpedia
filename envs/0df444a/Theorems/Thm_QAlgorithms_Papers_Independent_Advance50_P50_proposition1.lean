-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_proposition1
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.proposition1
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:04:48.808368+00:00
-- url     : https://prove2.me/theorems/0240e5de-755a-405b-b7df-22da1c78e058
-- title:
--   Seed paper result: Proposition 1, commutant sufficient condition
-- statement:
--   An $n$-qubit input $\rho$ is a positive semidefinite, trace-one matrix on the fixed computational basis, of dimension $d=2^n$. A $k$-copy model has a fixed input-independent unitary $U$, a Hermitian observable $O$, effective observable $\widetilde O=U^\dagger O U$, and exact response $h(\rho)=\operatorname{Tr}[U\rho^{\otimes k}U^\dagger O]$. Here $k\ge1$. The declared domain $R$ consists of density matrices, and its symmetry groups preserve $R$ and its binary labels. Invariance means equality of exact expectations on every $\rho\in R$ under the specified conjugation action. Write $C^{(k)}(G)=\{A:[A,V^{\otimes k}]=0\text{ for every }V\in G\}$. Then
--
--   $$\widetilde O\in C^{(k)}(G)\quad\Longrightarrow\quad h(V\rho V^\dagger)=h(\rho)\quad(V\in G,\rho\in R).$$
--
--   This is a sufficient structural condition for invariance; no converse is asserted.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 5, Seed paper result: Proposition 1, commutant sufficient condition

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

/-- PDF p.5, Proposition 1: tensorCommutant membership suffices for domain-relative invariance. -/
theorem proposition1 {n k : ℕ} (hk : 0 < k) (M : ExpectationModel (Qubits n) k)
    (G : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ))
    (R : Set (Mat (Qubits n))) (label : Mat (Qubits n) → Bool)
    (hdata : DatasetSymmetry (groupMatrices G) R label)
    (hcomm : M.effective ∈ tensorCommutant k (groupMatrices G)) :
    DomainInvariant (groupMatrices G) R M.response := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
