-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_lemma1
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.lemma1
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:22:58.234993+00:00
-- url     : https://prove2.me/theorems/6d845fcd-4bdb-40b2-93b0-bcb57eba0f1d
-- title:
--   Lemma 1: commutant closed under adjoints
-- statement:
--   Fix $n\ge0$, $k\ge1$, and a subgroup $G\subseteq U(2^n)$. For every complex operator $A$ on the $k$ copies,
--
--   $$A\in C^{(k)}(G)\quad\Longrightarrow\quad A^\dagger\in C^{(k)}(G).$$
--
--   There is no assumption that $A$ itself is Hermitian or nonzero. This supplies adjoint closure for the physical symmetry space.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 23, Lemma 1: commutant closed under adjoints

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

/-- PDF p.23, Lemma 1: unitary-group commutants are closed under adjoints. -/
theorem lemma1 {n k : ℕ} (hk : 0 < k)
    (G : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ))
    (A : Mat (Copies (Qubits n) k)) (hA : A ∈ tensorCommutant k (groupMatrices G)) :
    A.conjTranspose ∈ tensorCommutant k (groupMatrices G) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
