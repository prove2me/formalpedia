-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_proposition2
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.proposition2
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:05:51.141607+00:00
-- url     : https://prove2.me/theorems/1ce859c3-5bf1-4e76-bb54-e3207c918234
-- title:
--   Proposition 2: orthogonal Lie-algebra factors
-- statement:
--   An $n$-qubit input $\rho$ is a positive semidefinite, trace-one matrix on the fixed computational basis, of dimension $d=2^n$. A $k$-copy model has a fixed input-independent unitary $U$, a Hermitian observable $O$, effective observable $\widetilde O=U^\dagger O U$, and exact response $h(\rho)=\operatorname{Tr}[U\rho^{\otimes k}U^\dagger O]$. Here $k\ge1$. The declared domain $R$ consists of density matrices, and its symmetry groups preserve $R$ and its binary labels. Invariance means equality of exact expectations on every $\rho\in R$ under the specified conjugation action. Let $G$ be a represented unitary Lie group, $\mathfrak g$ its actual real tangent Lie algebra, and $iI\in\mathfrak g$. Its Hilbert–Schmidt complement $\mathfrak g^\perp$ is taken inside the skew-Hermitian matrices. Suppose $R\subseteq i\mathfrak g$. For every copy $j$, fix a Hermitian $A_j\in i\mathfrak g^\perp$ and an arbitrary operator $B_j$ on the other copies. Insert $A_j$ in copy $j$, preserving all other copy indices. If $\widetilde O$ belongs to the complex span of these specified separated terms, then
--
--   $$h(\rho)=h(V\rho V^\dagger)=0\quad(\rho\in R,V\in G).$$
--
--   Thus the model is invariant by orthogonality, independently of commutant membership.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 5, Proposition 2: orthogonal Lie-algebra factors

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

/-- PDF p.5, Proposition 2, Appendix B pp.23–24: factors orthogonal to the
actual Lie algebra force zero predictions, hence invariance.
Printed: PDF p.5 describes u(d) as skew-symmetric and writes exp(g)=G and g={X:exp(X) in G}.
Changed: Use the actual real skew-Hermitian tangent Lie algebra of the represented unitary group; keep iI in g, the stated orthogonal spaces, separated factors and the zero-output conclusion from Appendix B.
Why: The source means the unitary Lie algebra. A reflection is in O(d) but not exp(o(d)); the printed exponential rule cannot define the Lie algebra for the disconnected groups the paper uses. Tangents retain the adjoint-invariance argument without an exponential-surjectivity premise. -/
theorem proposition2 {n k : ℕ} (hk : 0 < k) (M : ExpectationModel (Qubits n) k)
    (L : MatrixLieData (Qubits n))
    (hidentity : Complex.I • (1 : Mat (Qubits n)) ∈ L.algebra)
    (R : Set (Mat (Qubits n))) (label : Mat (Qubits n) → Bool)
    (hdata : DatasetSymmetry (groupMatrices L.group) R label)
    (hinput : R ⊆ timesI (L.algebra : Set (Mat (Qubits n))))
    (A : Fin k → Mat (Qubits n))
    (B : (j : Fin k) → Mat ({c : Fin k // c ≠ j} → Qubits n))
    (hA : ∀ j, A j ∈ timesI (lieComplement L) ∧ (A j).IsHermitian)
    (hobs : M.effective ∈ separatedSpan A B) :
    DomainInvariant (groupMatrices L.group) R M.response ∧
      ∀ rho ∈ R, M.response rho = 0 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
