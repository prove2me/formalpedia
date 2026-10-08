-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch8_joint_tensor_representation
-- name    : TroppMatrixConcentration.ch8_joint_tensor_representation
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T14:48:41.669987+00:00
-- url     : https://prove2.me/theorems/a0e7d4df-4eaa-4042-8d09-33bf1ee8d4f5
-- title:
--   Relative entropy as a tensor perspective
-- statement:
--   For positive-definite complex matrices $A,H$ of the same dimension, $$D(A;H)=\Phi\bigl(\Psi_{-\log}(A\otimes I,I\otimes H^{\mathsf T})\bigr)-\operatorname{Re}\operatorname{tr}(A-H),$$ where $\Phi(M)=\operatorname{Re}(\operatorname{vec}(I)^*M\operatorname{vec}(I))$ and $\Psi_f$ is the matrix perspective. This identifies relative entropy with a positive functional applied to a matrix perspective.
-- source:
--   Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1, Sections 8.7–8.8, equation (8.8.1); uses the transpose required by complex vectorization conventions.

import Definitions.Def_TroppMatrixConcentration_ch8_joint_tensor
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TroppMatrixConcentration

theorem ch8_joint_tensor_representation {d : ℕ} [NeZero d]
    (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosDef) (hH : H.PosDef) :
    ch8_relativeEntropy A H =
      ch8_joint_eval (ch8_perspective (fun x => -Real.log x)
        (ch8_joint_left A) (ch8_joint_right H)) - (Matrix.trace (A - H)).re := by sorry

end TroppMatrixConcentration
