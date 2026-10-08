-- Prove2me | Theorems.Thm_RiemOpt_FR_theorem_2
-- name    : RiemOpt.FR.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:12.161123+00:00
-- url     : https://prove2.me/theorems/3cd854c9-cf2e-4dd0-ba80-607dd8185d7b
-- title:
--   Theorem 2 (Zoutendijk) on a Riemannian manifold — Σ cos²θ_k ‖Df(x_k)‖² < ∞ for Wolfe steps along descent directions
-- statement:
--   Let $\mathcal M$ be a smooth manifold modelled on a real Hilbert space, with a Riemannian metric, let $f:\mathcal M\to\mathbb R$ be differentiable and bounded below, and let $R$ be a retraction family. Consider a run of Algorithm 1: points $x_k\in\mathcal M$, descent directions $p_k\in T_{x_k}\mathcal M$ ($\mathrm Df(x_k)p_k<0$) and step lengths $\alpha_k>0$ with $x_{k+1}=R_{x_k}(\alpha_kp_k)$, where every $\alpha_k$ satisfies the Wolfe conditions (1a), (1b) with $0<c_1<c_2<1$. Suppose that the pull-backs $f_{R_{x_k}}=f\circ R_{x_k}$ are Lipschitz continuously differentiable on $\mathrm{span}\{p_k\}$ with a uniform Lipschitz constant $L>0$, i.e. $h_k(t)=f(R_{x_k}(tp_k))$ is differentiable and $|h_k'(s)-h_k'(t)|\le L|s-t|\,\|p_k\|_{x_k}^2$ for all $s,t$ and $k$. Then, with $\cos\theta_k=-\mathrm Df(x_k)p_k/(\|\mathrm Df(x_k)\|_{x_k}\|p_k\|_{x_k})$,
--   $$\sum_{k\in\mathbb N}\cos^2\theta_k\,\|\mathrm Df(x_k)\|_{x_k}^2<\infty.$$
--
--   Zoutendijk's theorem links the quality of the search directions to convergence: whenever the angles $\theta_k$ stay away from $\pi/2$ in a suitable averaged sense, the gradient norms must become small. It is the tool by which the Fletcher–Reeves result (Proposition 15) is proved.
--
--   **Formalization Note** "Lipschitz continuously differentiable on $\mathrm{span}\{p_k\}$" is read for the one-variable functions $h_k$; the factor $\|p_k\|^2$ converts the Lipschitz bound on the derivative of $f_{R_{x_k}}|_{\mathrm{span}\{p_k\}}$, a functional on the line, into a bound on $h_k'$. The constant is taken positive ($L>0$), the paper's reading. The run uses one retraction family for all $k$ and requires $\alpha_k>0$; boundedness below is `BddBelow (Set.range f)`, differentiability is `MDifferentiable`. The sum is expressed as `Summable` of the nonnegative terms.
-- source:
--   Ring, Wirth, Optimization Methods on Riemannian Manifolds and Their Application to Shape Space, SIAM J. Optim. 22 (2012), p. 601, Theorem 2

import Mathlib
import Definitions.Def_RiemOpt_FR_Setting

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.FR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

theorem theorem_2
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ) (L : ℝ)
    (hrun : IsWolfeRun f R c₁ c₂ x p α)
    (hbdd : BddBelow (Set.range f))
    (hL : 0 < L) (hlip : LineLipschitz f R x p L) :
    Summable (fun k : ℕ ↦ cosTheta f x p k ^ 2 * ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2) := by sorry

end RiemOpt.FR
