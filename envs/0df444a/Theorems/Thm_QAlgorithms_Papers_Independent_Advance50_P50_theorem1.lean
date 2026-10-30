-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_theorem1
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.theorem1
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:11:06.125573+00:00
-- url     : https://prove2.me/theorems/c25eb70c-b377-4eec-a8e7-e52e832f03d9
-- title:
--   Theorem 1: no informative one-copy purity model
-- statement:
--   An $n$-qubit input $\rho$ is a positive semidefinite, trace-one matrix on the fixed computational basis, of dimension $d=2^n$. A $k$-copy model has a fixed input-independent unitary $U$, a Hermitian observable $O$, effective observable $\widetilde O=U^\dagger O U$, and exact response $h(\rho)=\operatorname{Tr}[U\rho^{\otimes k}U^\dagger O]$. Fix $n\ge1$, $d=2^n$, and $1/d\le b<1$, with nonempty classes of purity $1$ and $b$. Write $R_b$ for their union and $p(\rho)=\operatorname{Tr}(\rho^2)$. For $k=1$, if the model is $U(d)$-invariant on $R_b$, then
--
--   $$h(\rho)=\frac{\operatorname{Tr}O}{d}\qquad(\rho\in R_b).$$
--
--   Every prediction is the same, so the model provides no label information. This applies to the stated single-unitary, single-expectation hypothesis class and asserts no impossibility for broader adaptive protocols.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 6, Theorem 1: no informative one-copy purity model

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

/-- PDF pp.6–7, Theorem 1 and Eq.(11): an invariant one-copy expectation is
constant on the full purity dataset and cannot convey label information. -/
theorem theorem1 {n : ℕ} (hn : 1 ≤ n) (b : ℝ)
    (hb : 1 / (2 : ℝ) ^ n ≤ b ∧ b < 1)
    (hpure : ∃ rho : Mat (Qubits n), IsDensityMatrix rho ∧ purity rho = 1)
    (hmixed : ∃ rho : Mat (Qubits n), IsDensityMatrix rho ∧ purity rho = b)
    (M : ExpectationModel (Qubits n) 1)
    (hinv : DomainInvariant (Matrix.unitaryGroup (Qubits n) ℂ : Set (Mat (Qubits n)))
      (purityDomain b) M.response) :
    ∀ rho ∈ purityDomain b, M.response rho = M.observable.trace.re / (2 : ℝ) ^ n := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
