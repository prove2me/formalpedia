-- Prove2me | Theorems.Thm_RiemOpt_FR_summable_grad4_div_dir2
-- name    : RiemOpt.FR.summable_grad4_div_dir2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:09.63479+00:00
-- url     : https://prove2.me/theorems/48e42f4d-4856-4584-818b-4f13d9fa63e0
-- title:
--   Proof of Proposition 15, p. 611 — Σ_k ‖Df(x_k)‖⁴/‖p_k‖² < ∞ for Riemannian Fletcher–Reeves
-- statement:
--   Consider a non-terminating Riemannian Fletcher–Reeves run as in Lemma 14 (strong Wolfe steps with $0<c_1<c_2<\tfrac12$, $\alpha_k>0$, $x_{k+1}=R_{x_k}(\alpha_kp_k)$, $p_0=-\nabla f(x_0)$, $p_{k+1}=-\nabla f(x_{k+1})+\beta_{k+1}T^{R_{x_k}}_{x_k,x_{k+1}}p_k$), and assume moreover the hypotheses of Theorem 2: $f$ is bounded below and the pull-backs $f_{R_{x_k}}$ are Lipschitz continuously differentiable on $\mathrm{span}\{p_k\}$ with a uniform constant $L>0$ (that is, $h_k(t)=f(R_{x_k}(tp_k))$ is differentiable with $|h_k'(s)-h_k'(t)|\le L|s-t|\,\|p_k\|_{x_k}^2$). Then
--   $$\sum_{k=0}^\infty\frac{\|\mathrm Df(x_k)\|_{x_k}^4}{\|p_k\|_{x_k}^2}<\infty.$$
--
--   This is the consequence of Zoutendijk's theorem that the proof of Proposition 15 contradicts when the gradient norms stay bounded away from zero.
--
--   **Formalization Note** The hypotheses of Theorem 2 (lower bound on $f$, uniform line-Lipschitz constant) are not among the conditions of Lemma 14; the paper's proof invokes Theorem 2 here, so they are stated explicitly. The sum is expressed as `Summable` of the nonnegative terms.
-- source:
--   Ring, Wirth, Optimization Methods on Riemannian Manifolds and Their Application to Shape Space, SIAM J. Optim. 22 (2012), p. 611, proof of Proposition 15

import Mathlib
import Definitions.Def_RiemOpt_FR_Setting

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.FR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

theorem summable_grad4_div_dir2
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (hrun : IsFRRun f R grad c₁ c₂ x p α) (hc₂ : c₂ < 1 / 2)
    (hbdd : BddBelow (Set.range f)) (L : ℝ) (hL : 0 < L) (hlip : LineLipschitz f R x p L) :
    Summable (fun k : ℕ ↦ ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 4 / ‖p k‖ ^ 2) := by sorry

end RiemOpt.FR
