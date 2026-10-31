-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P11_connectionGate_quadraticAlgebra
-- name    : QAlgorithms.Papers.Independent.Intake100.P11.connectionGate_quadraticAlgebra
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:55:20.181368+00:00
-- url     : https://prove2.me/theorems/6cd43aa5-df0d-470c-b93e-12ff5f7989ce
-- title:
--   Supporting algebra of the programmable connection gate
-- statement:
--   For real $k_1,k_2,\eta$, define $K=\begin{pmatrix}k_1-\eta&-\eta\\-\eta&k_2-\eta\end{pmatrix}$, $F_2=\begin{pmatrix}0&-I_2\\I_2&0\end{pmatrix}$, and the ideal grouped-coordinate matrix
--
--   $$
--   C(k_1,k_2,\eta)=F_2\begin{pmatrix}I_2&0\\K&I_2\end{pmatrix}
--   =\begin{pmatrix}-K&-I_2\\I_2&0\end{pmatrix}.
--   $$
--
--   This matrix preserves $F_2$ as a symplectic form. Its phase polynomial is $x^TKx=k_1x_1^2+k_2x_2^2-\eta(x_1+x_2)^2$, for every real position vector $x=(x_1,x_2)$. Every symmetric real $2\times2$ matrix is obtainable as $K$. Setting $\eta=0$ removes the intermode coupling and leaves independent elementary one-mode actions.
--
--   This supporting identity records the algebra needed by the source construction. The operational claim about this module on every normal two-mode input remains deferred in HARD.md; it is not replaced by a covariance or matrix assertion.
-- source:
--   Universal linear Bogoliubov transformations through one-way quantum computation, arXiv:0910.0660v1, PDF p. 8, §VI, Eq.(16)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P11

noncomputable section

open scoped Matrix BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P11

/-- PDF p.8, Eq.(16): SUPPORTING ideal connection algebra, including every
symmetric position-quadratic gate and disabling eta. The operational node is
deferred, not replaced by this identity. Corrected prose sign documented above. -/
theorem connectionGate_quadraticAlgebra :
    (∀ kappa1 kappa2 eta : ℝ,
      connectionMatrix kappa1 kappa2 eta =
        Matrix.fromBlocks (-(connectionQuadratic kappa1 kappa2 eta)) (-1 : Mat2) 1 0 ∧
      (connectionMatrix kappa1 kappa2 eta).transpose * fourierTwo *
        connectionMatrix kappa1 kappa2 eta = fourierTwo ∧
      ∀ x : Fin 2 → ℝ,
        (∑ i, ∑ j, x i * connectionQuadratic kappa1 kappa2 eta i j * x j) =
          kappa1 * (x 0) ^ 2 + kappa2 * (x 1) ^ 2 - eta * (x 0 + x 1) ^ 2) ∧
    (∀ K : Mat2, K.transpose = K →
      ∃ kappa1 kappa2 eta : ℝ, connectionQuadratic kappa1 kappa2 eta = K) ∧
    (∀ kappa1 kappa2 : ℝ,
      connectionMatrix kappa1 kappa2 0 =
        Matrix.fromBlocks (!![-kappa1, 0; 0, -kappa2] : Mat2) (-1 : Mat2) 1 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P11

end
