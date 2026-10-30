-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_hamiltonian_characterization
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.hamiltonian_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:07:04.667692+00:00
-- url     : https://prove2.me/theorems/6ae3c303-1b56-4fd2-8875-236875b33060
-- title:
--   Theorem 9: complete U(1) Hamiltonian characterization
-- statement:
--   Let 2≤k≤n and let H be a Hermitian n-qubit Hamiltonian commuting with total Z. Define C_l as the unnormalized sum of all Pauli Z strings of weight l. Then
--
--   $$\left(\forall t\in\mathbb R,\ e^{-itH}\in V_k\right)\quad\Longleftrightarrow\quad\operatorname{Tr}(HC_l)=0\quad(k<l\le n).$$
--
--   For k=n the constraint set is empty. This gives both necessity and sufficiency for the entire evolution family.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 9, Theorem 9 (also IV.C unnumbered theorem): complete U(1) Hamiltonian characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.23–24, Theorem 9/C5: the full necessary-and-sufficient condition;
when k=n there are no high-body constraints. -/
theorem hamiltonian_characterization (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (H : QMat n) (hH : H.IsHermitian) (hSym : U1Invariant H) :
    (∀ t : ℝ, schrodingerEvolution H t ∈ u1Group n k) ↔
      ∀ l : ℕ, k < l → l ≤ n → Matrix.trace (H * u1Central n l) = 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
