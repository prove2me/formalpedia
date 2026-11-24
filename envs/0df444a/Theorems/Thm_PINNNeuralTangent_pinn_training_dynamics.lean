-- Prove2me | Theorems.Thm_PINNNeuralTangent_pinn_training_dynamics
-- name    : PINNNeuralTangent.pinn_training_dynamics
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T10:11:32.978836+00:00
-- url     : https://prove2.me/theorems/2e01db6a-58f6-4c6f-a8b4-64d5675e79fb
-- title:
--   Lemma 3.1: training dynamics of a PINN under gradient flow
-- statement:
--   Let $\Omega\subset\mathbb R^d$ be bounded, let $\mathcal L$ be any operator taking functions on $\mathbb R^d$ to functions on $\mathbb R^d$, and let $u(x,\theta)$ be a network with finitely many parameters. Take boundary points $x_b^i\in\partial\Omega$ ($i\le N_b$) and collocation points $x_r^j\in\Omega$ ($j\le N_r$). Assume that $\theta\mapsto u(x_b^i,\theta)$ and $\theta\mapsto\mathcal Lu(x_r^j,\theta)$ are differentiable. Let $\theta(t)$, $t\in[0,T]$ with $T>0$, solve the gradient flow $\theta'=-\nabla\mathcal L(\theta)$ of the PINN loss
--   $$\mathcal L(\theta)=\tfrac12\sum_i|u(x_b^i,\theta)-g(x_b^i)|^2+\tfrac12\sum_j|\mathcal Lu(x_r^j,\theta)-f(x_r^j)|^2.$$
--   Then $K_{ru}(t)=K_{ur}(t)^\top$, and for every $t\in[0,T]$
--   $$\frac{d}{dt}\begin{bmatrix}u(x_b,\theta(t))\\\mathcal Lu(x_r,\theta(t))\end{bmatrix}=-\begin{bmatrix}K_{uu}(t)&K_{ur}(t)\\K_{ru}(t)&K_{rr}(t)\end{bmatrix}\begin{bmatrix}u(x_b,\theta(t))-g(x_b)\\\mathcal Lu(x_r,\theta(t))-f(x_r)\end{bmatrix},$$
--   where $K(t)$ is the NTK of the PINN at $\theta(t)$.
--
--   This identity is the starting point of the kernel analysis: the NTK of a PINN governs how the boundary fit and the PDE residual evolve during training.
--
--   **Formalization Note** The paper does not specify the time domain of the gradient flow (3.7). Here it is on a time interval $[0,T]$, with one-sided derivatives at its endpoints. The differentiability of the outputs in $\theta$ is implicit in the paper.
-- source:
--   Wang, Yu and Perdikaris, When and why PINNs fail to train: A neural tangent kernel perspective, arXiv:2007.14527v1 (2020), Section 3.1, Lemma 3.1, eqs. (3.7)-(3.9), p. 4; proof in Appendix A, p. 18

import Mathlib
import Definitions.Def_PINNNeuralTangent_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace PINNNeuralTangent

theorem pinn_training_dynamics {d : ℕ} {P : Type*} [Fintype P] [DecidableEq P] {Nb Nr : ℕ}
    (Ω : Set (Fin d → ℝ)) (hΩ : Bornology.IsBounded Ω)
    (Lop : ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → (P → ℝ) → ℝ)
    (f g : (Fin d → ℝ) → ℝ) (xb : Fin Nb → Fin d → ℝ) (xr : Fin Nr → Fin d → ℝ)
    (hxb : ∀ i, xb i ∈ frontier Ω) (hxr : ∀ j, xr j ∈ Ω)
    (hu : ∀ i, Differentiable ℝ (bdryOutputs u xb i))
    (hLu : ∀ j, Differentiable ℝ (opOutputs Lop u xr j))
    (T : ℝ) (hT : 0 < T) (θ : ℝ → P → ℝ)
    (hθ : IsGradFlow (pinnLoss (bdryOutputs u xb) (opOutputs Lop u xr)
      (fun i => g (xb i)) (fun j => f (xr j))) θ T) :
    (∀ t, ntkBlock (opOutputs Lop u xr) (bdryOutputs u xb) (θ t) =
      (ntkBlock (bdryOutputs u xb) (opOutputs Lop u xr) (θ t)).transpose) ∧
    ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt
        (fun s => Sum.elim (fun i => u (xb i) (θ s)) (fun j => opOutput Lop u (xr j) (θ s)))
        (-(pinnNTK (bdryOutputs u xb) (opOutputs Lop u xr) (θ t)).mulVec
          (Sum.elim (fun i => u (xb i) (θ t) - g (xb i))
            (fun j => opOutput Lop u (xr j) (θ t) - f (xr j))))
        (Set.Icc 0 T) t := by sorry

end PINNNeuralTangent
