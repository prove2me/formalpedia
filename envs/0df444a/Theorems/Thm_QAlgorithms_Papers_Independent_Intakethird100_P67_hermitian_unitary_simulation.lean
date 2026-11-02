-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_hermitian_unitary_simulation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.hermitian_unitary_simulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:59:44.959588+00:00
-- url     : https://prove2.me/theorems/542aa716-479b-4f18-88d9-a275314c3d89
-- title:
--   Appendix C, Eqs.(C10)–(C11): exponentiating a Hermitian unitary
-- statement:
--   Let $V$ be Hermitian and unitary, $\theta\in\mathbb R$, and let $V^c$ be its controlled version. For the ancillary Pauli $X$,
--
--   $$V^c(I\otimes e^{i\theta X})V^c=e^{i\theta V\otimes X},\qquad V^c(I\otimes e^{i\theta X})V^c(|\psi\rangle|+\rangle)=(e^{i\theta V}|\psi\rangle)|+\rangle.$$
--
--   The second identity holds for every normalized system vector. Tensor factors are displayed system first. Thus two controlled-$V$ applications and one ancillary rotation realize the exponential, returning the extra ancilla exactly to $|+\rangle$. The positive sign is intentional.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 20, Appendix C, Eqs.(C10)–(C11): exponentiating a Hermitian unitary

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF pp.20–21, C10–C11: the exponential has the intentional plus sign; the extra
ancilla returns to |plus> after two systemControlled-V gates and one ancillary rotation. -/
theorem hermitian_unitary_simulation (V : Matrix.unitaryGroup I ℂ)
    (hV : (V : Matrix I I ℂ).IsHermitian) (theta : ℝ) (psi : EuclideanSpace ℂ I) (hpsi : IsState psi) :
    systemControlled (V : Matrix I I ℂ) * Matrix.kronecker (1 : Matrix I I ℂ) (positivePhaseEvolution pauliX theta) *
      systemControlled (V : Matrix I I ℂ) = positivePhaseEvolution (Matrix.kronecker (V : Matrix I I ℂ) pauliX) theta ∧
    act (systemControlled (V : Matrix I I ℂ) * Matrix.kronecker (1 : Matrix I I ℂ) (positivePhaseEvolution pauliX theta) *
      systemControlled (V : Matrix I I ℂ)) (tensorVec psi (act hadamard (ket false))) =
      tensorVec (act (positivePhaseEvolution (V : Matrix I I ℂ) theta) psi) (act hadamard (ket false)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
