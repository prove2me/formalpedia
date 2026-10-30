-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_symmetric_projective_measurements
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.symmetric_projective_measurements
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:11:23.372437+00:00
-- url     : https://prove2.me/theorems/dc8d045e-d03f-47b0-ba70-43001e3009e3
-- title:
--   Corollary 13: invariant rank-one projective measurements
-- statement:
--   Let n≥1 and let {φ_v} be an orthonormal basis of n-qubit states, each lying in one Hamming-weight sector, with the sector allowed to depend on v. There is W∈G_2 and a permutation b of computational labels such that, for every state ψ and basis label v,
--
--   $$|\langle b(v)|W|\psi\rangle|^2=|\langle\phi_v|\psi\rangle|^2.$$
--
--   Thus the full labeled projective measurement is realized by a finite exchange/Z circuit followed by computational-basis measurements, without an ancilla.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 34, Corollary 13: arbitrary U(1)-invariant rank-one projective measurements

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.34, Corollary 13: a basis unitary whose columns have definite charge.
The final computational labels may be permuted; every input Born probability agrees. -/
theorem symmetric_projective_measurements (n : ℕ) (hn : 1 ≤ n) (B : QMat n)
    (hB : B ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hCharge : ∀ v : Qubits n, ∃ m : Fin (n+1),
      ∀ x : Qubits n, qubitWeight x ≠ m.val → B x v = 0) :
    ∃ W : QMat n, W ∈ xyZGroup n ∧ ∃ labels : Equiv.Perm (Qubits n),
      ∀ (psi : EuclideanSpace ℂ (Qubits n)) (v : Qubits n),
        Complex.normSq (act W psi (labels v)) =
          Complex.normSq (∑ x : Qubits n, conj (B x v) * psi x) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
