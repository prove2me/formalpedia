-- Prove2me | Theorems.Thm_RiemProxGrad_Global_eq_3_9
-- name    : RiemProxGrad.Global.eq_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:17.567021+00:00
-- url     : https://prove2.me/theorems/03bdea20-ff76-4768-aa24-d6f4b2571f3f
-- title:
--   (3.9) — $\operatorname{grad} f(x_{k+1})-\mathcal T^{-\sharp}(\operatorname{grad} f(x_k)+\tilde L\eta^*_{x_k})=\operatorname{grad} f(x_{k+1})+\zeta_{x_{k+1}}\in\partial F(x_{k+1})$
-- statement:
--   In the setting of Algorithm 1 (finite-dimensional Riemannian manifold $\mathcal M$ with smooth metric, smooth retraction $R$, $F = f + g$ with $f\in C^1$ and $g$ continuous with locally Lipschitz pull-backs $g\circ R_x$, constants $0<\tilde L$, $L<\tilde L$), let $(x_k,\eta^*_{x_k})$ be a run of Algorithm 1 and $k$ an iteration at which the vector transport by differentiated retraction $\mathcal T_{R_{\eta^*_{x_k}}} = DR_{x_k}(\eta^*_{x_k})$ is invertible. Let $\zeta_{x_{k+1}}\in\partial g(x_{k+1})$ satisfy (3.8), where $x_{k+1} = R_{x_k}(\eta^*_{x_k})$. Then
--   $$\operatorname{grad} f(R_{x_k}(\eta^*_{x_k})) - \mathcal T^{-\sharp}_{R_{\eta^*_{x_k}}}\big(\operatorname{grad} f(x_k) + \tilde L\,\eta^*_{x_k}\big) = \operatorname{grad} f(x_{k+1}) + \zeta_{x_{k+1}} \in \partial F(x_{k+1}). \qquad (3.9)$$
--
--   This produces, from the subproblem's optimality condition, an explicit Riemannian subgradient of $F$ at the new iterate. With Lemma 3.2 and (3.6) it tends to $0$ along a convergent subsequence, which is how Theorem 3.1 obtains stationarity of accumulation points.
--
--   **Formalization Note** The paper states (3.9) along a subsequence $k_j$ for $j$ large, where invertibility of the transport follows from the retraction being a diffeomorphism on a ball of a totally retractive neighbourhood; here invertibility is the hypothesis and the statement is for any such $k$. The point $x_{k+1}$ is written $R_{x_k}(\eta^*_{x_k})$, equal to it by the run.
-- source:
--   Huang, Wei, Riemannian proximal gradient methods, arXiv:1909.06065v4, p. 8, proof of Theorem 3.1, (3.9)

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting
import Definitions.Def_RiemOpt_FR_Setting
import Definitions.Def_RiemProxGrad_Global_Setting

open Bundle Manifold Filter Topology
open scoped ContDiff

namespace RiemProxGrad.Global

/-- (3.9), proof of Theorem 3.1 (Huang–Wei, arXiv:1909.06065v4, p. 8): if the vector transport by
differentiated retraction `T_{R_{η*_{x_k}}}` is invertible and `ζ ∈ ∂g(x_{k+1})` satisfies (3.8),
then, with `x_{k+1} = R_{x_k}(η*_{x_k})`,
`grad f(R_{x_k}(η*_{x_k})) − T^{−♯}(grad f(x_k) + L̃ η*_{x_k}) = grad f(x_{k+1}) + ζ ∈ ∂F(x_{k+1})`. -/
theorem eq_3_9 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    {R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M} {f g : M → ℝ}
    {grad : (x : M) → TangentSpace 𝓘(ℝ, E) x} {L Lt : ℝ}
    {x : ℕ → M} {η : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)}
    (hS : Standing R f g grad) (hLt : 0 < Lt) (hL : L < Lt)
    (hrun : IsRPGRun R g grad Lt x η) (k : ℕ)
    (hT : (RiemOpt.BFGS.transport R (x k) (η k)).IsInvertible)
    (ζ : TangentSpace 𝓘(ℝ, E) (R (x k) (η k))) (hζ : ζ ∈ riemSubdiff R g (R (x k) (η k)))
    (h38 : grad (x k) + Lt • η k + transportAdj R (x k) (η k) ζ = 0) :
    grad (R (x k) (η k)) - transportInvAdj R (x k) (η k) (grad (x k) + Lt • η k) =
        grad (R (x k) (η k)) + ζ ∧
      grad (R (x k) (η k)) + ζ ∈ riemSubdiff R (f + g) (R (x k) (η k)) := by sorry

end RiemProxGrad.Global
