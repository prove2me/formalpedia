-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_learning_response
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.learning_response
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:27:52.708857+00:00
-- url     : https://prove2.me/theorems/88fffe9c-355c-4cca-a89f-0e00ab43e0cc
-- title:
--   Finite leading dQNTK learning response and bound
-- statement:
--   The circuit acts on a nonzero finite-dimensional complex Hilbert space $H=\mathbb C^h$ and has the ordered form $U(\theta)=\prod_{\ell=1}^L W_\ell\exp(i\theta_\ell X_\ell)$, with fixed unitary $W_\ell$, Hermitian $X_\ell$, and real angles. Products are written in increasing index order and the rightmost factor acts first. Feature vectors $\phi(x)$ have norm one. For Hermitian observables $O_i$, put $z_{x,i}(\theta)=\langle U(\theta)\phi(x),O_iU(\theta)\phi(x)\rangle\in\mathbb R$.
--
--   Absorb the reference angles into the fixed gates and set $\theta=\delta\varphi$, where $\delta>0$. Write $J_{a\ell}=\partial_{\varphi_\ell}z_a(0)$ and $H_{a,k\ell}=\partial_{\varphi_k}\partial_{\varphi_\ell}z_a(0)$ for derivatives of the actual circuit. The frozen kernel is $K_{ab}=\sum_\ell J_{a\ell}J_{b\ell}$.
--
--   Let $A$ be a finite training subset of the data space and let $I$ be the finite observable index set. All matrices in the training recurrence are restricted to $A\times I$. For initial rescaled angles $v$, put
--   $$
--   D_{ab}=\sum_{\ell,k}\bigl(J_{a\ell}H_{b,k\ell}+H_{a,k\ell}J_{b\ell}\bigr)v_k.
--   $$
--   The initial residual $e$ is the quadratic Taylor output at $v$ minus the real training labels. The retained coefficient dynamics are $F_0=e$, $I_0=0$, $F_{t+1}=(1-\eta K)F_t$, and $I_{t+1}=(1-\eta K)I_t-\eta DF_t$. Thus the retained residual is $F_t+I_t$.
--
--   For $\eta>0$, set $B=1-\eta K$. Then
--   $$
--   F_t=B^t e,\qquad I_0=0,\qquad
--   I_{t+1}=-\eta\sum_{s=0}^{t}B^{t-s}DB^s e,\qquad
--   \|I_{t+1}\|_2\le\eta(t+1)\|B\|_2^t\|D\|_2\|e\|_2.
--   $$
--   This is the fixed-time leading response in the retained perturbative model. It supplies no higher-order remainder estimate for exact nonlinear training.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 6, Main Theorem 4; Eqs.(35)-(39); SM Eqs.(114)-(118)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF p.6 Theorem 4 Eqs.(35)-(39), SM pp.26-27 Eqs.(114)-(118): leading retained
coefficient response and L2 bound at each finite time. No exact nonlinear GD equality,
uniform-in-time remainder or unsupported source component shorthand is used. -/
theorem learning_response {D T I : Type*} [Fintype T] [DecidableEq T]
    [Fintype I] [DecidableEq I] {h L : ℕ}
    (M : ExpectationNetwork D I h L) (embed : T ↪ D)
    (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 < eta)
    (v : Fin L → ℝ) (y : T × I → ℝ) :
    let K := trainingKernel M delta embed
    let D : Matrix (T × I) (T × I) ℝ := fun a b =>
      deltaKernel M delta v (trainingIndex embed a) (trainingIndex embed b)
    let e : EuclideanSpace ℝ (T × I) := WithLp.toLp 2
      (fun a => quadraticOutput M delta v (trainingIndex embed a) - y a)
    let R := retainedResidual K D eta e
    (∀ t, (R t).1 = l2Action ((1 - eta • K) ^ t) e) ∧
    (R 0).2 = 0 ∧
    (∀ t : ℕ, (R (t + 1)).2 = -eta •
      (∑ s ∈ Finset.range (t + 1),
        l2Action (((1 - eta • K) ^ (t - s)) * D * ((1 - eta • K) ^ s)) e)) ∧
    ∀ t : ℕ, ‖(R (t + 1)).2‖ ≤ eta * ((t : ℝ) + 1) *
      QAlgorithms.specNorm (1 - eta • K) ^ t * QAlgorithms.specNorm D * ‖e‖ := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
