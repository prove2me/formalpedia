-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_hermitian_parts
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.hermitian_parts
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:23:54.680817+00:00
-- url     : https://prove2.me/theorems/e6a71aaf-7844-461c-b48b-3439be430c10
-- title:
--   Appendix A: two Hermitian parts remain in the commutant
-- statement:
--   Fix $n\ge0$, $k\ge1$, a unitary subgroup $G$, and $A\in C^{(k)}(G)$. Then
--
--   $$A+A^\dagger,\quad i(A-A^\dagger)\ \text{are Hermitian elements of }C^{(k)}(G).$$
--
--   If $A\ne0$, at least one of these two operators is nonzero. At $A=0$ only the Hermiticity and membership conclusions are asserted. This does not assert a nonzero projection onto one preselected Hermitian component.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 23, Appendix A: two Hermitian parts remain in the commutant

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

/-- PDF p.23, Appendix A: both Hermitian parts remain in the tensorCommutant.
For nonzero A at least one part is nonzero; neither individual projection
is asserted nonzero. -/
theorem hermitian_parts {n k : ℕ} (hk : 0 < k)
    (G : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ))
    (A : Mat (Copies (Qubits n) k)) (hA : A ∈ tensorCommutant k (groupMatrices G)) :
    (A + A.conjTranspose).IsHermitian ∧
    (Complex.I • (A - A.conjTranspose)).IsHermitian ∧
    A + A.conjTranspose ∈ tensorCommutant k (groupMatrices G) ∧
    Complex.I • (A - A.conjTranspose) ∈ tensorCommutant k (groupMatrices G) ∧
    (A ≠ 0 → A + A.conjTranspose ≠ 0 ∨ Complex.I • (A - A.conjTranspose) ≠ 0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
