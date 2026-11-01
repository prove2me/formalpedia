-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_optimization_kernel_identity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.optimization_kernel_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:23:55.760533+00:00
-- url     : https://prove2.me/theorems/d47de671-ae22-4eb3-bea8-052d01043669
-- title:
--   Optimization QNTK: nonnegativity and commutator identity
-- statement:
--   The circuit acts on a nonzero finite-dimensional complex Hilbert space $H=\mathbb C^h$ and has the ordered form $U(\theta)=\prod_{\ell=1}^L W_\ell\exp(i\theta_\ell X_\ell)$, with fixed unitary $W_\ell$, Hermitian $X_\ell$, and real angles. Products are written in increasing index order and the rightmost factor acts first. Feature vectors $\phi(x)$ have norm one. For Hermitian observables $O_i$, put $z_{x,i}(\theta)=\langle U(\theta)\phi(x),O_iU(\theta)\phi(x)\rangle\in\mathbb R$.
--
--   In the scalar optimization problem, the state is a fixed normalized $\Psi_0$, the observable is $O$, and its known minimum eigenvalue is $O_0$. Put $\epsilon=z-O_0$. Let $P_\ell=\prod_{k<\ell}W_k e^{i\theta_kX_k}$, $S_\ell=\prod_{k>\ell}W_ke^{i\theta_kX_k}$, $F_\ell=W_\ell e^{i\theta_\ell X_\ell}$, and $B_\ell=F_\ell^\dagger P_\ell^\dagger O P_\ell F_\ell$. With $\Theta_\ell=\langle\Psi_0|S_\ell^\dagger[X_\ell,B_\ell]S_\ell|\Psi_0\rangle$, one has
--   $$
--   \operatorname{Re}\Theta_\ell=0,\qquad \partial_{\theta_\ell}\epsilon=-i\Theta_\ell,\qquad K=\sum_\ell(\partial_{\theta_\ell}\epsilon)^2=-\sum_\ell\Theta_\ell^2\ge0.
--   $$
--   This identifies the scalar optimization kernel as a nonnegative Gram quantity.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 3, Eq.(5); SM Eqs.(58)-(59)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF p.3 Eq.(5), SM pp.19-20 Eqs.(58)-(59): K is nonnegative and is minus the
sum of squared imaginary commutator expectations. The printed main Eq.(5) omits the sum
in its second display; the derivative definition and multioutput Eq.(29) specify it. -/
theorem optimization_kernel_identity {h L : ℕ} (M : OptimizationModel h L)
    (theta : Fin L → ℝ) :
    0 ≤ expectationKernel M.model theta ((), ()) ((), ()) ∧
    (∀ l, (thetaCoefficient M.model theta ((), ()) l).re = 0 ∧
      (coordinateDerivative (fun u => expectationOutput M.model u ((), ()) - M.minimum) theta l : ℂ) =
        -Complex.I * thetaCoefficient M.model theta ((), ()) l) ∧
    (expectationKernel M.model theta ((), ()) ((), ()) : ℂ) =
      -∑ l, thetaCoefficient M.model theta ((), ()) l ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
