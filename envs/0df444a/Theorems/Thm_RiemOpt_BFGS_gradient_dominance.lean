-- Prove2me | Theorems.Thm_RiemOpt_BFGS_gradient_dominance
-- name    : RiemOpt.BFGS.gradient_dominance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:30.622899+00:00
-- url     : https://prove2.me/theorems/9aecb41b-83b3-4506-b9d6-3a10cbb484ec
-- title:
--   Appendix A, proof of Proposition 10, p. 622 — f(x) − f(x*) ≤ ‖Df(x)‖²/(2m) on the sublevel set
-- statement:
--   Let $\mathcal M$ be a Riemannian manifold modelled on a Hilbert space, $R$ a retraction family, $f:\mathcal M\to\mathbb R$ differentiable, and $x,x_0\in\mathcal M$ with $f(x)\le f(x_0)$. Assume that $f_{R_x}=f\circ R_x$ is $C^2$, that the set $S=R_x^{-1}(\{f\le f(x_0)\})\subseteq T_x\mathcal M$ is convex, and that for some $m>0$
--   $$\mathrm D^2f_{R_x}(p)(v,v)\ge m\|v\|_x^2\qquad\text{for all }p\in S,\ v\in T_x\mathcal M.$$
--   Let $x^*$ be a global minimizer of $f$ that lies in the image of $R_x$. Then
--   $$f(x)-f(x^*)\le\frac{1}{2m}\|\mathrm Df(x)\|_x^2 .$$
--
--   This gradient-dominance (Polyak–Łojasiewicz) inequality converts the decrease $f(x_i)-f(x_{i+1})\gtrsim\|\mathrm Df(x_i)\|^2$ at good indices into a contraction of $f(x_i)-f(x^*)$.
--
--   **Formalization Note** The paper states the inequality for a generic $x$ and obtains it by minimizing a Taylor expansion over $\hat x$; it uses $R_x^{-1}(\hat x)$ at $\hat x=x^*$. Here the reachability of $x^*$ from $x$ by $R_x$ is an explicit hypothesis (it holds for $R=\exp$ on a complete finite-dimensional manifold but is not automatic). Only the lower Hessian bound is needed. In the proof of Proposition 10 the inequality is applied at the iterates $x=x_i$.
-- source:
--   Ring, Wirth, Optimization Methods on Riemannian Manifolds and Their Application to Shape Space, SIAM J. Optim. 22 (2012), p. 622, Appendix A, proof of Proposition 10

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting

open Bundle Manifold
open scoped ContDiff

namespace RiemOpt.BFGS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

theorem gradient_dominance
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (hR : IsRetraction R)
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f)
    (x x₀ xstar : M) (m : ℝ) (hm : 0 < m)
    (hC2 : ContDiff ℝ 2 (f ∘ R x))
    (hconv : Convex ℝ {q : TangentSpace 𝓘(ℝ, E) x | f (R x q) ≤ f x₀})
    (hlow : ∀ q : TangentSpace 𝓘(ℝ, E) x, f (R x q) ≤ f x₀ →
      ∀ v : TangentSpace 𝓘(ℝ, E) x, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (f ∘ R x)) q v v)
    (hx : f x ≤ f x₀) (hmin : ∀ y : M, f xstar ≤ f y)
    (hreach : ∃ q : TangentSpace 𝓘(ℝ, E) x, R x q = xstar) :
    f x - f xstar ≤ ‖Df (E := E) f x‖ ^ 2 / (2 * m) := by sorry

end RiemOpt.BFGS
