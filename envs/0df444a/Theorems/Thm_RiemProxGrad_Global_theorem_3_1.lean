-- Prove2me | Theorems.Thm_RiemProxGrad_Global_theorem_3_1
-- name    : RiemProxGrad.Global.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:34.135852+00:00
-- url     : https://prove2.me/theorems/dc4cc41c-5bd3-4e8f-901c-4865902dea89
-- title:
--   Theorem 3.1 — accumulation points of RPG are stationary; $\|\eta^*_{x_k}\|\le\epsilon$ within $(F(x_0)-F(x_*))/(\beta\epsilon^2)$ iterations
-- statement:
--   Let $\mathcal M$ be a finite-dimensional Riemannian manifold with smooth metric and $R$ a smooth retraction. Consider $F = f + g$, where $f$ is continuously differentiable with Riemannian gradient $\operatorname{grad} f$, and $g$ is continuous with each pull-back $g\circ R_x$ locally Lipschitz on $T_x\mathcal M$. Let $0<\tilde L$, $L<\tilde L$, $\beta = (\tilde L - L)/2$, and let $(x_k,\eta^*_{x_k})_{k\ge0}$ be any run of the Riemannian proximal gradient method (Algorithm 1) with constant $\tilde L$. A point $x$ is stationary when $0\in\partial F(x)$, the Riemannian Clarke subdifferential.
--
--   1. If $\eta^*_{x_k} = 0$, then $x_k$ is a stationary point.
--
--   Suppose moreover Assumption 3.1 ($F$ bounded below, $\Omega_{x_0} = \{x\mid F(x)\le F(x_0)\}$ compact) and Assumption 3.2 ($f$ is $L$-retraction-smooth on $\Omega_{x_0}$). Then:
--
--   2. the sequence $\{x_k\}$ has at least one accumulation point;
--   3. every accumulation point $x_*$ of $\{x_k\}$ is a stationary point;
--   4. for every $\epsilon>0$ and every accumulation point $x_*$, Algorithm 1 returns $x_k$ with $\|\eta^*_{x_k}\|_{x_k}\le\epsilon$ in at most
--   $$\frac{F(x_0) - F(x_*)}{\beta\,\epsilon^2}$$
--   iterations, i.e. for some index $k \le (F(x_0)-F(x_*))/(\beta\epsilon^2)$.
--
--   This is the global convergence result for RPG: it extends the stationarity of limit points and the $O(1/\epsilon^2)$ iteration complexity of the Euclidean proximal gradient method to manifolds, with a nonconvex $g$ and a subproblem that is only solved to stationarity.
--
--   **Formalization Note** "Accumulation point" is `MapClusterPt` of the sequence along `atTop`. "In at most $N$ iterations" is read as an index $k$ with $k\le N$ (the proof gives $k\le\lceil N\rceil-1$ when $N>0$). Assumption 3.2 is in the strengthened reading described in the definition file: (3.2) at every $x\in\Omega_{x_0}$ for every $\eta\in T_x\mathcal M$. Part 1 is stated without Assumptions 3.1–3.2, as in the paper.
-- source:
--   Huang, Wei, Riemannian proximal gradient methods, arXiv:1909.06065v4, p. 8, Theorem 3.1

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting
import Definitions.Def_RiemOpt_FR_Setting
import Definitions.Def_RiemProxGrad_Global_Setting

open Bundle Manifold Filter Topology
open scoped ContDiff

namespace RiemProxGrad.Global

/-- Theorem 3.1 (Huang–Wei, arXiv:1909.06065v4, p. 8). For every run of Algorithm 1:
if `η*_{x_k} = 0` then `x_k` is a stationary point of `F = f + g`. Under Assumptions 3.1 and 3.2,
`{x_k}` has an accumulation point, every accumulation point `x*` is stationary, and for every
`ε > 0` some `k ≤ (F(x₀) − F(x*))/(βε²)`, `β = (L̃ − L)/2`, has `‖η*_{x_k}‖_{x_k} ≤ ε`. -/
theorem theorem_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    {R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M} {f g : M → ℝ}
    {grad : (x : M) → TangentSpace 𝓘(ℝ, E) x} {L Lt : ℝ}
    {x : ℕ → M} {η : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)}
    (hS : Standing R f g grad) (hLt : 0 < Lt) (hL : L < Lt)
    (hrun : IsRPGRun R g grad Lt x η) :
    (∀ k : ℕ, η k = 0 → IsStationary R (f + g) (x k)) ∧
    (Assumption31 f g (x 0) → Assumption32 R f g grad L (x 0) →
      (∃ xs : M, MapClusterPt xs atTop x) ∧
      (∀ xs : M, MapClusterPt xs atTop x → IsStationary R (f + g) xs) ∧
      (∀ ε : ℝ, 0 < ε → ∀ xs : M, MapClusterPt xs atTop x →
        ∃ k : ℕ, (k : ℝ) ≤ ((f + g) (x 0) - (f + g) xs) / ((Lt - L) / 2 * ε ^ 2) ∧
          ‖η k‖ ≤ ε)) := by sorry

end RiemProxGrad.Global
