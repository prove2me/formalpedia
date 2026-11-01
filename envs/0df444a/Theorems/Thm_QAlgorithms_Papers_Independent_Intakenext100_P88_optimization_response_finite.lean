-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_optimization_response_finite
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.optimization_response_finite
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:26:51.554044+00:00
-- url     : https://prove2.me/theorems/30861f27-c212-456d-a161-cd2b2a1c8a08
-- title:
--   Finite scalar dQNTK coefficient response
-- statement:
--   The circuit acts on a nonzero finite-dimensional complex Hilbert space $H=\mathbb C^h$ and has the ordered form $U(\theta)=\prod_{\ell=1}^L W_\ell\exp(i\theta_\ell X_\ell)$, with fixed unitary $W_\ell$, Hermitian $X_\ell$, and real angles. Products are written in increasing index order and the rightmost factor acts first. Feature vectors $\phi(x)$ have norm one. For Hermitian observables $O_i$, put $z_{x,i}(\theta)=\langle U(\theta)\phi(x),O_iU(\theta)\phi(x)\rangle\in\mathbb R$.
--
--   Absorb the reference angles into the fixed gates and set $\theta=\delta\varphi$, where $\delta>0$. Write $J_{a\ell}=\partial_{\varphi_\ell}z_a(0)$ and $H_{a,k\ell}=\partial_{\varphi_k}\partial_{\varphi_\ell}z_a(0)$ for derivatives of the actual circuit. The frozen kernel is $K_{ab}=\sum_\ell J_{a\ell}J_{b\ell}$.
--
--   In scalar optimization with known minimum eigenvalue $O_0$, let $e=z(0)+\sum_\ell J_\ell v_\ell+\frac12\sum_{k,\ell}H_{k\ell}v_kv_\ell-O_0$ and $D=2\sum_{k,\ell}J_\ell H_{k\ell}v_k$. For $\eta>0$, define the retained coefficient dynamics by $F_0=e$, $I_0=0$, $F_{t+1}=(1-\eta K)F_t$ and $I_{t+1}=(1-\eta K)I_t-\eta DF_t$. Then
--   $$
--   F_t=(1-\eta K)^t e,\qquad I_0=0,\qquad I_{t+1}=-\eta(t+1)(1-\eta K)^tDe.
--   $$
--   This gives the fixed-time leading perturbative response without asserting convergence of exact nonlinear training or a uniform-in-time remainder.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 22, SM Eqs.(78)-(81); main Eqs.(19)-(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF pp.4-5 Eqs.(19)-(21), SM p.22 Eqs.(78)-(81): fixed-time retained scalar
response. K and D are computed from the circuit jets. The t=0 interacting part is separate;
there is no truncated natural exponent and no asserted all-time nonlinear error estimate. -/
theorem optimization_response_finite {h L : ℕ} (M : OptimizationModel h L)
    (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 < eta) (v : Fin L → ℝ) :
    let K := frozenKernel M.model delta ((), ()) ((), ())
    let D := deltaKernel M.model delta v ((), ()) ((), ())
    let e := quadraticOutput M.model delta v ((), ()) - M.minimum
    let R := retainedResidual (fun _ _ : Unit => K) (fun _ _ : Unit => D)
      eta (WithLp.toLp 2 (fun _ : Unit => e))
    (∀ t, (R t).1 () = (1 - eta * K) ^ t * e) ∧
    (R 0).2 = 0 ∧
    ∀ t : ℕ, (R (t + 1)).2 () =
      -eta * ((t : ℝ) + 1) * (1 - eta * K) ^ t * D * e := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
