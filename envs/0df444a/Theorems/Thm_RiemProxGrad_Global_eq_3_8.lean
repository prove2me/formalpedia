-- Prove2me | Theorems.Thm_RiemProxGrad_Global_eq_3_8
-- name    : RiemProxGrad.Global.eq_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:16:02.38846+00:00
-- url     : https://prove2.me/theorems/e23d73cd-35d4-43d8-9278-b604c0856834
-- title:
--   (3.8) — optimality of the RPG step: $\operatorname{grad} f(x_k)+\tilde L\eta^*_{x_k}+\mathcal T^\sharp_{R_{\eta^*_{x_k}}}\zeta_{x_{k+1}}=0$
-- statement:
--   In the setting of Algorithm 1 (finite-dimensional Riemannian manifold $\mathcal M$ with smooth metric, smooth retraction $R$, $F = f + g$ with $f\in C^1$ and $g$ continuous with locally Lipschitz pull-backs $g\circ R_x$, constants $0<\tilde L$, $L<\tilde L$), let $(x_k,\eta^*_{x_k})$ be a run of Algorithm 1. Then for every $k$ there is a Riemannian subgradient $\zeta_{x_{k+1}}\in\partial g(x_{k+1})$, where $x_{k+1} = R_{x_k}(\eta^*_{x_k})$, such that
--   $$\operatorname{grad} f(x_k) + \tilde L\,\eta^*_{x_k} + \mathcal T^\sharp_{R_{\eta^*_{x_k}}}\zeta_{x_{k+1}} = 0. \qquad (3.8)$$
--   Here $\mathcal T^\sharp_{R_{\eta^*_{x_k}}} : T_{x_{k+1}}\mathcal M\to T_{x_k}\mathcal M$ is the adjoint of the vector transport by differentiated retraction $DR_{x_k}(\eta^*_{x_k})$.
--
--   This is the first-order optimality condition of the proximal subproblem (3.1), written with a subgradient of $g$ at the new iterate. It holds at every iteration, with no condition on the step size.
--
--   **Formalization Note** The subdifferential is taken at $R_{x_k}(\eta^*_{x_k})$, which equals $x_{k+1}$ by the run; writing it this way keeps the adjoint's domain $T_{R_{x_k}(\eta^*_{x_k})}\mathcal M$ literally the fibre of $\zeta$. No invertibility of the transport is assumed.
-- source:
--   Huang, Wei, Riemannian proximal gradient methods, arXiv:1909.06065v4, p. 8, proof of Theorem 3.1, (3.8)

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting
import Definitions.Def_RiemOpt_FR_Setting
import Definitions.Def_RiemProxGrad_Global_Setting

open Bundle Manifold Filter Topology
open scoped ContDiff

namespace RiemProxGrad.Global

/-- (3.8), proof of Theorem 3.1 (Huang–Wei, arXiv:1909.06065v4, p. 8): for every iteration `k` of
Algorithm 1 there is `ζ ∈ ∂g(x_{k+1})`, `x_{k+1} = R_{x_k}(η*_{x_k})`, with
`grad f(x_k) + L̃ η*_{x_k} + T^♯_{R_{η*_{x_k}}} ζ = 0`. -/
theorem eq_3_8 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    {R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M} {f g : M → ℝ}
    {grad : (x : M) → TangentSpace 𝓘(ℝ, E) x} {L Lt : ℝ}
    {x : ℕ → M} {η : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)}
    (hS : Standing R f g grad) (hLt : 0 < Lt) (hL : L < Lt)
    (hrun : IsRPGRun R g grad Lt x η) (k : ℕ) :
    ∃ ζ ∈ riemSubdiff R g (R (x k) (η k)),
      grad (x k) + Lt • η k + transportAdj R (x k) (η k) ζ = 0 := by sorry

end RiemProxGrad.Global
