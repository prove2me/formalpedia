-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_multiple_groups
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.multiple_groups
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:10:09.073793+00:00
-- url     : https://prove2.me/theorems/c42c2576-bb65-4a8b-b60e-ba3fab634efd
-- title:
--   Unnumbered extension to a family of groups
-- statement:
--   An $n$-qubit input $\rho$ is a positive semidefinite, trace-one matrix on the fixed computational basis, of dimension $d=2^n$. A $k$-copy model has a fixed input-independent unitary $U$, a Hermitian observable $O$, effective observable $\widetilde O=U^\dagger O U$, and exact response $h(\rho)=\operatorname{Tr}[U\rho^{\otimes k}U^\dagger O]$. Here $k\ge1$. The declared domain $R$ consists of density matrices, and its symmetry groups preserve $R$ and its binary labels. Invariance means equality of exact expectations on every $\rho\in R$ under the specified conjugation action. Let $(G_j)_{j\in J}$ be any indexed family, with declared stable domains $R_j$. If the same fixed effective observable belongs to each commutant, then
--
--   $$\bigl(\forall j\in J,\ \widetilde O\in C^{(k)}(G_j)\bigr)\ \Longrightarrow\ \forall j\in J,\ h\text{ is }G_j\text{-invariant on }R_j.$$
--
--   The same model works for every group in the family. For an empty index set the statement is vacuous, as is the source's all-groups condition.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 6, Unnumbered extension to a family of groups

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

/-- PDF p.6: the tensorCommutant criterion extends to any family of symmetry groups. -/
theorem multiple_groups {n k : ℕ} (hk : 0 < k) (M : ExpectationModel (Qubits n) k)
    {J : Type*} (G : J → Subgroup (Matrix.unitaryGroup (Qubits n) ℂ))
    (R : J → Set (Mat (Qubits n))) (label : Mat (Qubits n) → Bool)
    (hdata : ∀ j, DatasetSymmetry (groupMatrices (G j)) (R j) label)
    (hcomm : ∀ j, M.effective ∈ tensorCommutant k (groupMatrices (G j))) :
    ∀ j, DomainInvariant (groupMatrices (G j)) (R j) M.response := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
