-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_frozen_optimization_finite
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.frozen_optimization_finite
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T08:26:16.374137+00:00
-- url     : https://prove2.me/theorems/dccdf5ed-530d-4c45-bfd8-2f18d0f4a3c7
-- title:
--   Finite frozen scalar optimization solution
-- statement:
--   The circuit acts on a nonzero finite-dimensional complex Hilbert space $H=\mathbb C^h$ and has the ordered form $U(\theta)=\prod_{\ell=1}^L W_\ell\exp(i\theta_\ell X_\ell)$, with fixed unitary $W_\ell$, Hermitian $X_\ell$, and real angles. Products are written in increasing index order and the rightmost factor acts first. Feature vectors $\phi(x)$ have norm one. For Hermitian observables $O_i$, put $z_{x,i}(\theta)=\langle U(\theta)\phi(x),O_iU(\theta)\phi(x)\rangle\in\mathbb R$.
--
--   Absorb the reference angles into the fixed gates and set $\theta=\delta\varphi$, where $\delta>0$. Write $J_{a\ell}=\partial_{\varphi_\ell}z_a(0)$ and $H_{a,k\ell}=\partial_{\varphi_k}\partial_{\varphi_\ell}z_a(0)$ for derivatives of the actual circuit. The frozen kernel is $K_{ab}=\sum_\ell J_{a\ell}J_{b\ell}$.
--
--   For scalar optimization, let $O_0$ be the known minimum eigenvalue of $O$ and let $e=z(0)+\sum_\ell J_\ell v_\ell-O_0$ be the initial frozen residual at rescaled angles $v$. Under the frozen recurrence $\epsilon_{t+1}=\epsilon_t-\eta K\epsilon_t$, with $\eta>0$, one has
--   $$
--   \epsilon_t=(1-\eta K)^t e,\qquad t\in\mathbb N.
--   $$
--   The identity permits $K=0$, when the residual stays constant. It is the independently displayed finite solution, without the invalid unconditional convergence assertion of the full printed Theorem 1.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 21, SM Eq.(69); main Eq.(10)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF p.3 Eq.(10), SM p.21 Eq.(69): finite frozen scalar solution.
This independent displayed identity does not include Theorem 1's invalid unconditional
zero-limit assertion. K=0 and L=0 are allowed and give constant residuals. -/
theorem frozen_optimization_finite {h L : ℕ} (M : OptimizationModel h L)
    (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 < eta)
    (v : Fin L → ℝ) (t : ℕ) :
    let K := frozenKernel M.model delta ((), ()) ((), ())
    let e := linearOutput M.model delta v ((), ()) - M.minimum
    frozenResidual (fun _ _ : Unit => K) eta (WithLp.toLp 2 (fun _ : Unit => e)) t () =
      (1 - eta * K) ^ t * e := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
