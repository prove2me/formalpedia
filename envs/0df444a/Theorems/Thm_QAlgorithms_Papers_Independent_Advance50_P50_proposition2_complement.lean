-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_proposition2_complement
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.proposition2_complement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:07:00.525994+00:00
-- url     : https://prove2.me/theorems/a4bd0076-ba52-471c-9b35-8d5bb911b1ce
-- title:
--   Unnumbered complementary case of Proposition 2
-- statement:
--   An $n$-qubit input $\rho$ is a positive semidefinite, trace-one matrix on the fixed computational basis, of dimension $d=2^n$. A $k$-copy model has a fixed input-independent unitary $U$, a Hermitian observable $O$, effective observable $\widetilde O=U^\dagger O U$, and exact response $h(\rho)=\operatorname{Tr}[U\rho^{\otimes k}U^\dagger O]$. Here $k\ge1$. The declared domain $R$ consists of density matrices, and its symmetry groups preserve $R$ and its binary labels. Invariance means equality of exact expectations on every $\rho\in R$ under the specified conjugation action. Let $\mathfrak g$ be the actual tangent Lie algebra of $G$ and $\mathfrak g^\perp$ its Hilbert–Schmidt complement inside the skew-Hermitian matrices. Assume $iI\in\mathfrak g^\perp$ and $R\subseteq i\mathfrak g^\perp$. For each copy fix Hermitian $A_j\in i\mathfrak g$ and arbitrary complementary-copy operator $B_j$. If $\widetilde O$ lies in their separated-term span, then
--
--   $$h(\rho)=h(V\rho V^\dagger)=0\quad(\rho\in R,V\in G).$$
--
--   The complementary space is a real vector space, with no Lie-algebra assumption.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 5, Unnumbered complementary case of Proposition 2

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

/-- PDF p.5, complementary case, Eq.(B8) p.24: interchange the two orthogonal
real spaces. The complement is not assumed to be a Lie algebra.
Printed: PDF p.24 after Eq.(B8) writes Tr[rho V-dagger A_j V] in ig; the p.5 Lie-algebra exposition uses the erroneous exponential rule.
Changed: Read V-dagger A_j V as the matrix in ig, and use the actual tangent algebra. Retain iI in g-perp, rho in i(g-perp), A_j in ig and both zero and invariance conclusions.
Why: The trace is a scalar, whereas ig is a matrix space. The displayed B8 calculation and the following adjoint-invariance explanation uniquely identify the missing matrix; no trace-zero assertion is added as a hypothesis. -/
theorem proposition2_complement {n k : ℕ} (hk : 0 < k) (M : ExpectationModel (Qubits n) k)
    (L : MatrixLieData (Qubits n))
    (hidentity : Complex.I • (1 : Mat (Qubits n)) ∈ lieComplement L)
    (R : Set (Mat (Qubits n))) (label : Mat (Qubits n) → Bool)
    (hdata : DatasetSymmetry (groupMatrices L.group) R label)
    (hinput : R ⊆ timesI (lieComplement L))
    (A : Fin k → Mat (Qubits n))
    (B : (j : Fin k) → Mat ({c : Fin k // c ≠ j} → Qubits n))
    (hA : ∀ j, A j ∈ timesI (L.algebra : Set (Mat (Qubits n))) ∧ (A j).IsHermitian)
    (hobs : M.effective ∈ separatedSpan A B) :
    DomainInvariant (groupMatrices L.group) R M.response ∧
      ∀ rho ∈ R, M.response rho = 0 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
