-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_proposition3
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.proposition3
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:08:24.625015+00:00
-- url     : https://prove2.me/theorems/46404809-caae-4827-9a9a-1b81eb50c996
-- title:
--   Proposition 3: two commutant conditions
-- statement:
--   An $n$-qubit input $\rho$ is a positive semidefinite, trace-one matrix on the fixed computational basis, of dimension $d=2^n$. A $k$-copy model has a fixed input-independent unitary $U$, a Hermitian observable $O$, effective observable $\widetilde O=U^\dagger O U$, and exact response $h(\rho)=\operatorname{Tr}[U\rho^{\otimes k}U^\dagger O]$. Here $k\ge1$. The declared domain $R$ consists of density matrices, and its symmetry groups preserve $R$ and its binary labels. Invariance means equality of exact expectations on every $\rho\in R$ under the specified conjugation action. Let $G_0,G_1$ act on their respective stable domains $R_0,R_1$. Then
--
--   $$\widetilde O\in C^{(k)}(G_0)\cap C^{(k)}(G_1)\ \Longrightarrow\ h\text{ is invariant under both actions}.$$
--
--   For either $i\in\{0,1\}$, membership in $C^{(k)}(G_i)$ together with nonmembership in $C^{(k)}(G_{1-i})$ still guarantees $G_i$-invariance on $R_i$. It does not establish non-invariance under the other group. This distinguishes a sufficient criterion from a converse.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 6, Proposition 3: two commutant conditions

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

/-- PDF p.6, Proposition 3, Appendix C p.24. Nonmembership in the other
tensorCommutant does not imply failure of invariance. Both index orders are included. -/
theorem proposition3 {n k : ℕ} (hk : 0 < k) (M : ExpectationModel (Qubits n) k)
    (G : Bool → Subgroup (Matrix.unitaryGroup (Qubits n) ℂ))
    (R : Bool → Set (Mat (Qubits n))) (label : Mat (Qubits n) → Bool)
    (hdata : ∀ i, DatasetSymmetry (groupMatrices (G i)) (R i) label) :
    ((∀ i, M.effective ∈ tensorCommutant k (groupMatrices (G i))) →
      ∀ i, DomainInvariant (groupMatrices (G i)) (R i) M.response) ∧
    (∀ i, M.effective ∈ tensorCommutant k (groupMatrices (G i)) →
      M.effective ∉ tensorCommutant k (groupMatrices (G (!i))) →
      DomainInvariant (groupMatrices (G i)) (R i) M.response) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
