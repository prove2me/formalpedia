-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_theorem9
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.theorem9
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:24:47.682907+00:00
-- url     : https://prove2.me/theorems/076445ab-288d-472e-8f80-5c19e7153e41
-- title:
--   Theorem 9: ancilla purity classifier
-- statement:
--   Fix $n\ge1$, $d=2^n$, and $1/d\le b<1$, with nonempty classes of purity $1$ and $b$. Write $R_b$ for their union and $p(\rho)=\operatorname{Tr}(\rho^2)$. Use an ancilla initially in $|0\rangle$, two copies of $\rho$, and an ancilla-only Hermitian measurement. There is a fixed input-independent realization $U=(H\otimes I)\,\mathrm{CSWAP}\,(H\otimes I)$ and ancilla observable $Z$ such that
--
--   $$U^\dagger(Z\otimes I)U=Z\otimes\mathrm{SWAP},\qquad Z|0\rangle=|0\rangle,\qquad h(\rho)=\operatorname{Tr}(\rho^2).$$
--
--   The model is $U(d)$-invariant on all density matrices and perfectly separates the purity classes in exact expectation. This is the existential realization in the theorem; it does not assert realizability of every tensor $A\otimes S$ by an ancilla-only measurement.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 25, Theorem 9: ancilla purity classifier

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

/-- PDF pp.25–26, Theorem 9: an actual ancilla-only realization with A=Z,
S=SWAP, unit eigenvalue on |0>, exact purity response and perfect separation.
The statement does not assume every A,S has an ancilla-only realization. -/
theorem theorem9 {n : ℕ} (hn : 1 ≤ n) (b : ℝ)
    (hb : 1 / (2 : ℝ) ^ n ≤ b ∧ b < 1)
    (hpure : ∃ rho : Mat (Qubits n), IsDensityMatrix rho ∧ purity rho = 1)
    (hmixed : ∃ rho : Mat (Qubits n), IsDensityMatrix rho ∧ purity rho = b) :
    ∃ M : AncillaModel (Qubits n),
      (M.unitary : Mat (Bool × Copies (Qubits n) 2)) = swapTestMatrix (Qubits n) ∧
      M.observable = pauliZ ∧
      M.effective = Matrix.kronecker pauliZ (copySwap (Qubits n)) ∧
      act pauliZ (ket false) = ket false ∧
      DomainInvariant (Matrix.unitaryGroup (Qubits n) ℂ : Set (Mat (Qubits n)))
        {rho | IsDensityMatrix rho} M.response ∧
      (∀ rho, IsDensityMatrix rho → M.response rho = purity rho) ∧
      SeparatesPurity b M.response := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
