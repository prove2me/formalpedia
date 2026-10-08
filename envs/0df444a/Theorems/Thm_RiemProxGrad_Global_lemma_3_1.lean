-- Prove2me | Theorems.Thm_RiemProxGrad_Global_lemma_3_1
-- name    : RiemProxGrad.Global.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:36.906096+00:00
-- url     : https://prove2.me/theorems/b912e95e-25d2-4935-b199-5ea5121df1bf
-- title:
--   Lemma 3.1 — RPG descent: $F(x_k)-F(x_{k+1})\ge\beta\|\eta^*_{x_k}\|^2_{x_k}$, $\beta=(\tilde L-L)/2$
-- statement:
--   Let $\mathcal M$ be a finite-dimensional Riemannian manifold, $R$ a smooth retraction, $F = f + g$ with $f$ continuously differentiable (Riemannian gradient $\operatorname{grad} f$) and $g$ continuous with locally Lipschitz pull-backs $g\circ R_x$. Let $0 < \tilde L$ and $L < \tilde L$, and let $(x_k, \eta^*_{x_k})_{k\ge 0}$ be a run of the Riemannian proximal gradient method (Algorithm 1) with constant $\tilde L$. Suppose Assumption 3.2 holds: $f$ is $L$-retraction-smooth on the sublevel set $\Omega_{x_0} = \{x \mid F(x)\le F(x_0)\}$. Then for every $k$,
--   $$F(x_k) - F(x_{k+1}) \ge \beta\,\|\eta^*_{x_k}\|_{x_k}^2,\qquad \beta = \frac{\tilde L - L}{2}. \qquad (3.5)$$
--
--   So RPG is a descent method, without any convexity of $g$, and the decrease is controlled by the squared length of the step. This is the basic inequality behind the global convergence analysis of Theorem 3.1.
--
--   **Formalization Note** Assumption 3.2 is taken in the reading the proof uses: $f(R_x(\eta)) \le f(x) + \langle\operatorname{grad} f(x),\eta\rangle_x + \frac L2\|\eta\|_x^2$ for every $x\in\Omega_{x_0}$ and every $\eta\in T_x\mathcal M$ (`Assumption32`). This strengthens Definition 3.1 read literally, under which the lemma is false. That $x_k\in\Omega_{x_0}$ is part of what must be shown, not a hypothesis.
-- source:
--   Huang, Wei, Riemannian proximal gradient methods, arXiv:1909.06065v4, p. 7, Lemma 3.1 (3.5)

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting
import Definitions.Def_RiemOpt_FR_Setting
import Definitions.Def_RiemProxGrad_Global_Setting

open Bundle Manifold Filter Topology
open scoped ContDiff

namespace RiemProxGrad.Global

/-- Lemma 3.1 (Huang–Wei, arXiv:1909.06065v4, p. 7): under Assumption 3.2, every run of Algorithm 1
satisfies `F(x_k) − F(x_{k+1}) ≥ β‖η*_{x_k}‖²_{x_k}` with `β = (L̃ − L)/2` (3.5). Assumption 3.2 is
taken in the reading of the proof: (3.2) at every `x ∈ Ω_{x₀}` and every `η ∈ T_xM`. -/
theorem lemma_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    {R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M} {f g : M → ℝ}
    {grad : (x : M) → TangentSpace 𝓘(ℝ, E) x} {L Lt : ℝ}
    {x : ℕ → M} {η : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)}
    (hS : Standing R f g grad) (hLt : 0 < Lt) (hL : L < Lt)
    (hA32 : Assumption32 R f g grad L (x 0)) (hrun : IsRPGRun R g grad Lt x η) (k : ℕ) :
    (f + g) (x k) - (f + g) (x (k + 1)) ≥ (Lt - L) / 2 * ‖η k‖ ^ 2 := by sorry

end RiemProxGrad.Global
