-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_amplitude_kernel_psd
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.amplitude_kernel_psd
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T08:25:04.957222+00:00
-- url     : https://prove2.me/theorems/e1df25ae-70f7-4920-addb-1d31ac5c19df
-- title:
--   Doubled amplitude QNTK is Hermitian and positive semidefinite
-- statement:
--   Use the same ordered unitary circuit and normalized feature states, but output all complex amplitudes $z_{x,i}=\langle i|U\phi(x)\rangle$, $i=1,\ldots,h$. Duplicate each output as $\mathcal z_{x,0,i}=z_{x,i}$ and $\mathcal z_{x,1,i}=\overline{z_{x,i}}$. The worldsheet index therefore records whether an amplitude is conjugated. For real parameters, write $\mathcal J_{\mu\ell}=\partial_{\theta_\ell}\mathcal z_\mu$.
--
--   Define $\mathcal K_{\mu\nu}=\sum_\ell\mathcal J_{\mu\ell}\overline{\mathcal J_{\nu\ell}}$. If $J$ is the undoubled amplitude Jacobian, its blocks are
--   $$
--   \mathcal K=\begin{pmatrix}JJ^\dagger&JJ^T\\\overline J J^\dagger&\overline J J^T\end{pmatrix}.
--   $$
--   This kernel is Hermitian, and every finite Gram submatrix is positive semidefinite for arbitrary complex test vectors. This extends kernel positivity to complex amplitude outputs without asserting invertibility.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 29, SM Theorem 2; Eqs.(135),(141)-(142)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF p.29 SM Theorem 2, Eqs.(135),(141)-(142): the doubled complex kernel is Hermitian
and PSD on arbitrary finite submatrices, not just on conjugate-paired test vectors. -/
theorem amplitude_kernel_psd {D : Type*} {h L : ℕ}
    (M : AmplitudeModel D h L) (theta : Fin L → ℝ) :
    (∀ a b, star (amplitudeKernel M theta b a) = amplitudeKernel M theta a b) ∧
    ∀ (n : ℕ) (a : Fin n → D × Bool × Fin h),
      Matrix.PosSemidef (fun i j => amplitudeKernel M theta (a i) (a j)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
