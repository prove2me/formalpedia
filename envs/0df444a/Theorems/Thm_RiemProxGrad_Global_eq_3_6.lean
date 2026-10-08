-- Prove2me | Theorems.Thm_RiemProxGrad_Global_eq_3_6
-- name    : RiemProxGrad.Global.eq_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:54.222699+00:00
-- url     : https://prove2.me/theorems/a71d1c4b-0ee7-482d-89ad-73acad37dd2e
-- title:
--   (3.6) — the RPG steps vanish: $\lim_{k\to\infty}\|\eta^*_{x_k}\|_{x_k}=0$
-- statement:
--   In the setting of Algorithm 1 (finite-dimensional Riemannian manifold $\mathcal M$, smooth retraction $R$, $F = f + g$ with $f\in C^1$ and $g$ continuous with locally Lipschitz pull-backs $g\circ R_x$, constants $0<\tilde L$, $L<\tilde L$), suppose Assumption 3.1 ($F$ bounded below, $\Omega_{x_0}$ compact) and Assumption 3.2 ($f$ is $L$-retraction-smooth on $\Omega_{x_0}$) hold. Then every run $(x_k,\eta^*_{x_k})$ of Algorithm 1 satisfies
--   $$\lim_{k\to\infty} \|\eta^*_{x_k}\|_{x_k} = 0. \qquad (3.6)$$
--
--   This is the first step of the proof of Theorem 3.1: summing the descent inequality (3.5) shows that the squared step lengths are summable. It is what makes the subproblem optimality condition (3.8) converge to a stationarity condition along a convergent subsequence.
--
--   **Formalization Note** Assumption 3.2 is in the strengthened reading described in the definition file. Only boundedness from below is needed; $F$ is not assumed to attain its minimum.
-- source:
--   Huang, Wei, Riemannian proximal gradient methods, arXiv:1909.06065v4, p. 8, proof of Theorem 3.1, (3.6)

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting
import Definitions.Def_RiemOpt_FR_Setting
import Definitions.Def_RiemProxGrad_Global_Setting

open Bundle Manifold Filter Topology
open scoped ContDiff

namespace RiemProxGrad.Global

/-- (3.6), proof of Theorem 3.1 (Huang–Wei, arXiv:1909.06065v4, p. 8): under Assumptions 3.1 and
3.2, the steps of Algorithm 1 vanish, `lim_{k → ∞} ‖η*_{x_k}‖_{x_k} = 0`. -/
theorem eq_3_6 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    {R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M} {f g : M → ℝ}
    {grad : (x : M) → TangentSpace 𝓘(ℝ, E) x} {L Lt : ℝ}
    {x : ℕ → M} {η : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)}
    (hS : Standing R f g grad) (hLt : 0 < Lt) (hL : L < Lt)
    (hA31 : Assumption31 f g (x 0)) (hA32 : Assumption32 R f g grad L (x 0))
    (hrun : IsRPGRun R g grad Lt x η) :
    Tendsto (fun k => ‖η k‖) atTop (𝓝 0) := by sorry

end RiemProxGrad.Global
