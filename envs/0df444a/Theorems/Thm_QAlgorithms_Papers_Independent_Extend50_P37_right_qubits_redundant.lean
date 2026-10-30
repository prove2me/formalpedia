-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_right_qubits_redundant
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.right_qubits_redundant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:41:42.098969+00:00
-- url     : https://prove2.me/theorems/739d6c27-5610-4d71-85bc-fefa2117d9c9
-- title:
--   V B 3: the right qubits carry no additional decision information
-- statement:
--   Let $b$ be uniform on $\{0,1\}$ and $V$ Haar-uniform on $U(2)$. Prepare $n\ge1$ copies of $(I\otimes V)|\psi_b\rangle$, with $\psi_0=|00\rangle$ and $\psi_1=(|01\rangle+|10\rangle)/\sqrt2$. Every POVM $M$ on both sets of qubits admits a POVM $N$ on the $n$ left qubits with
--   $$\int_{U(2)}\operatorname{tr}(M(B)\rho_{b,V}^{\otimes n})\,dV
--   =\operatorname{tr}(N(B)\rho_{L,b}^{\otimes n}),\quad\rho_{L,0}=|0\rangle\langle0|,\quad\rho_{L,1}=I/2.$$
--   This holds for both branches and every measurable event. The unitary is shared by all copies. Collective left-qubit measurements remain allowed; information in the right qubits is redundant for this decision problem.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 25, V B 3: the right qubits carry no additional decision information

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF p.25, V B 3: collective measurements on the left qubits reproduce
every conditional outcome law of the full experiment; no separate-left-qubit
measurement claim is made. The Haar unitary is shared by the n copies. -/
theorem right_qubits_redundant {O : Type*} [MeasurableSpace O]
    (n : ℕ) (hn : 0 < n)
    (M : Measurements.OperatorPOVM (Fin n → Fin 2 × Fin 2) O) :
    ∃ N : Measurements.OperatorPOVM (Fin n → Fin 2) O,
      ∀ b : Fin 2, ∀ B, MeasurableSet B →
        (∫ V : Matrix.unitaryGroup (Fin 2) ℂ,
          effectProb (M.operator B) (piKron n (twoQubitOrbit b (V : Mat (Fin 2))))
          ∂Schur.unitaryHaar 2) = effectProb (N.operator B) (piKron n (decisionMarginal b)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
