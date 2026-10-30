-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_proposition4
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.proposition4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:09:09.314808+00:00
-- url     : https://prove2.me/theorems/f3c6d782-07a6-4ecd-8187-8bfacc279a15
-- title:
--   Proposition 4: two Lie-algebra conditions
-- statement:
--   An $n$-qubit input $\rho$ is a positive semidefinite, trace-one matrix on the fixed computational basis, of dimension $d=2^n$. A $k$-copy model has a fixed input-independent unitary $U$, a Hermitian observable $O$, effective observable $\widetilde O=U^\dagger O U$, and exact response $h(\rho)=\operatorname{Tr}[U\rho^{\otimes k}U^\dagger O]$. Here $k\ge1$. The declared domain $R$ consists of density matrices, and its symmetry groups preserve $R$ and its binary labels. Invariance means equality of exact expectations on every $\rho\in R$ under the specified conjugation action. Let $G_0,G_1$ be represented unitary Lie groups with actual algebras $\mathfrak g_0,\mathfrak g_1$. For each $i$, choose $D_i$ to be either $\mathfrak g_i$ or $\mathfrak g_i^\perp$, and $F_i$ the other space. Assume $iI\in D_i$ and $R\subseteq iD_0\cap iD_1$. For fixed Hermitian factors $A_j$ and complementary-copy operators $B_j$, assume $\widetilde O\in\operatorname{span}\{A_j\otimes B_j\}_j$, with the factors inserted in their actual slots. Then
--
--   $$\bigl(\forall i,j,\ A_j\in iF_i\bigr)\ \Longrightarrow\ h\text{ is both }G_0\text{- and }G_1\text{-invariant on }R.$$
--
--   For either $i$, if all $A_j$ belong to $iF_i$ and not to $iF_{1-i}$, $G_i$-invariance still follows. This includes the source's complementary-space extension and makes no converse claim.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 6, Proposition 4: two Lie-algebra conditions

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

/-- PDF p.6, Proposition 4, including its complementary-space extension.
The common-domain guarantee and both one-sided cases are stated. Printed
`igi` is the other indexed algebra; no failure of the other invariance follows.
Printed: PDF pp.6,24 prints rho in ig0,igi and G0(1)/G1(0); p.5 also gives an erroneous exponential definition of the algebras.
Changed: Use the actual tangent algebras, a common domain in both indexed input spaces, both index orders, and an explicit Bool flag for each stated algebra/complement exchange.
Why: Appendix C reduces the two cases to Proposition 2. The index typo cannot denote an additional independent algebra. The changes only make those two cases and the explicitly stated complementary-space extension precise; nonmembership never becomes a claim of non-invariance. -/
theorem proposition4 {n k : ℕ} (hk : 0 < k) (M : ExpectationModel (Qubits n) k)
    (L : Bool → MatrixLieData (Qubits n)) (complementary : Bool → Bool)
    (hidentity : ∀ i, Complex.I • (1 : Mat (Qubits n)) ∈
      inputLieSpace (L i) (complementary i))
    (R : Set (Mat (Qubits n))) (label : Mat (Qubits n) → Bool)
    (hdata : ∀ i, DatasetSymmetry (groupMatrices (L i).group) R label)
    (hinput : ∀ i, R ⊆ timesI (inputLieSpace (L i) (complementary i)))
    (A : Fin k → Mat (Qubits n))
    (B : (j : Fin k) → Mat ({c : Fin k // c ≠ j} → Qubits n))
    (hA : ∀ j, (A j).IsHermitian) (hobs : M.effective ∈ separatedSpan A B) :
    ((∀ i j, A j ∈ timesI (inputLieSpace (L i) (!(complementary i)))) →
      ∀ i, DomainInvariant (groupMatrices (L i).group) R M.response) ∧
    (∀ i, (∀ j, A j ∈ timesI (inputLieSpace (L i) (!(complementary i)))) →
      (∀ j, A j ∉ timesI (inputLieSpace (L (!i)) (!(complementary (!i))))) →
      DomainInvariant (groupMatrices (L i).group) R M.response) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
