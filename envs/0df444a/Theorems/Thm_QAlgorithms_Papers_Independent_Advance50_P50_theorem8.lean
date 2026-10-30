-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_theorem8
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.theorem8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:20:42.517443+00:00
-- url     : https://prove2.me/theorems/56cccd6b-4d1b-433a-82f5-bd4bde63939d
-- title:
--   Theorem 8: permutation-invariant single-copy models
-- statement:
--   An $n$-qubit input $\rho$ is a positive semidefinite, trace-one matrix on the fixed computational basis, of dimension $d=2^n$. A $k$-copy model has a fixed input-independent unitary $U$, a Hermitian observable $O$, effective observable $\widetilde O=U^\dagger O U$, and exact response $h(\rho)=\operatorname{Tr}[U\rho^{\otimes k}U^\dagger O]$. Let $n\ge0$ and define $\mathcal V_n=\operatorname{span}_{\mathbb C}\{A^{\otimes n}:A\in U(2)\}$. Every Hermitian $B\in\mathcal V_n$ has a one-copy realization with effective observable $B$, and
--
--   $$h(P\rho P^\dagger)=h(\rho)\quad(P\in S_n,\ \rho\text{ a density matrix}).$$
--
--   The span is of the whole set of collective unitaries, not one preselected tensor power. This guarantees invariance only, without asserting separation of arbitrary encoded graph classes.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 15, Theorem 8: permutation-invariant single-copy models

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

/-- PDF p.15, Theorem 8 and Eq.(43): every Hermitian element of the full
collective-unitary span can be realized by a permutation-invariant H1 model.
No graph classification guarantee is inferred. -/
theorem theorem8 (n : ℕ) :
    ∀ A : Mat (Qubits n), A.IsHermitian → A ∈ collectiveSpan n →
      ∃ M : ExpectationModel (Qubits n) 1,
        M.effective = (fun x y => A (x 0) (y 0)) ∧
        DomainInvariant (sitePermutationMatrices n) {rho | IsDensityMatrix rho} M.response := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
