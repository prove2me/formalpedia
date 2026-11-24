-- Prove2me | Theorems.Thm_PINNNeuralTangent_wide_network_gaussian_process
-- name    : PINNNeuralTangent.wide_network_gaussian_process
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T10:12:22.28379+00:00
-- url     : https://prove2.me/theorems/998d5ae8-206d-4842-ac43-46087b946cff
-- title:
--   Theorem 4.1: $u$ and $u_{xx}$ of a wide network are Gaussian processes
-- statement:
--   Let $\sigma$ be smooth with bounded second derivative $\ddot\sigma$. Let $u(x,\theta)$ be the one-hidden-layer network of width $N$ in NTK parameterization, with all parameters i.i.d. $\mathcal N(0,1)$. Then, as $N\to\infty$,
--   $$u(\cdot,\theta)\xrightarrow{\mathcal D}\mathcal{GP}(0,\Sigma^{(1)}),\qquad u_{xx}(\cdot,\theta)\xrightarrow{\mathcal D}\mathcal{GP}(0,\Sigma^{(1)}_{xx}),\qquad \Sigma^{(1)}_{xx}(x,x')=E_{u,v\sim\mathcal N(0,1)}\big[u^4\ddot\sigma(ux+v)\ddot\sigma(ux'+v)\big].$$
--   That is, for all points $x_1,\dots,x_n\in\mathbb R$, the law of $(u(x_1,\theta),\dots,u(x_n,\theta))$ converges weakly to $\mathcal N(0,[\Sigma^{(1)}(x_i,x_j)]_{ij})$, and the law of $(u_{xx}(x_1,\theta),\dots,u_{xx}(x_n,\theta))$ converges weakly to $\mathcal N(0,[\Sigma^{(1)}_{xx}(x_i,x_j)]_{ij})$.
--
--   So at initialization, an infinitely wide PINN for the model problem has Gaussian-process outputs and residual operator outputs.
--
--   **Formalization Note** Convergence in distribution of the processes is read as weak convergence of the finite-dimensional distributions. Weak convergence is written as convergence of $\int F$ for every bounded continuous $F$. The Gaussian limit is identified by its characteristic function. The points range over all of $\mathbb R$.
-- source:
--   Wang, Yu and Perdikaris, When and why PINNs fail to train: A neural tangent kernel perspective, arXiv:2007.14527v1 (2020), Section 4, Theorem 4.1, eqs. (4.4)-(4.6), p. 5; Σ^(1) from eq. (2.4), p. 3; proof in Appendix B, p. 19

import Mathlib
import Definitions.Def_PINNNeuralTangent_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace PINNNeuralTangent

theorem wide_network_gaussian_process (σ : ℝ → ℝ) (hσ : ContDiff ℝ ∞ σ)
    (hσ2 : ∃ C, ∀ z, |iteratedDeriv 2 σ z| ≤ C) {n : ℕ} (x : Fin n → ℝ) :
    (∃ γ : Measure (Fin n → ℝ), IsCenteredGaussian γ (Matrix.of fun i j => sigma1 σ (x i) (x j)) ∧
      ∀ F : BoundedContinuousFunction (Fin n → ℝ) ℝ,
        Tendsto (fun N : ℕ => ∫ θ, F (fun i => netU σ θ (x i)) ∂(initMeasure N)) atTop
          (𝓝 (∫ y, F y ∂γ))) ∧
    (∃ γ : Measure (Fin n → ℝ), IsCenteredGaussian γ (Matrix.of fun i j => sigmaXX σ (x i) (x j)) ∧
      ∀ F : BoundedContinuousFunction (Fin n → ℝ) ℝ,
        Tendsto (fun N : ℕ => ∫ θ, F (fun i => netUxx σ θ (x i)) ∂(initMeasure N)) atTop
          (𝓝 (∫ y, F y ∂γ))) := by sorry

end PINNNeuralTangent
