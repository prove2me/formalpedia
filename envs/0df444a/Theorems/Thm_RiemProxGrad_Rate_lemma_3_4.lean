-- Prove2me | Theorems.Thm_RiemProxGrad_Rate_lemma_3_4
-- name    : RiemProxGrad.Rate.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:10.412653+00:00
-- url     : https://prove2.me/theorems/75184c71-8b62-4760-95a7-eb0a04fa747b
-- title:
--   Lemma 3.4 — $F(z)\le F(y)+(\tilde L/2)(\|\xi_x\|^2-\|\xi_x-\eta^*_x\|^2)$ for the RPG step $z=R_x(\eta^*_x)$
-- statement:
--   Let $\mathcal M$ be a finite-dimensional Riemannian manifold with retraction $R$, and let $F=f+g$ with $f$ differentiable (gradient $\operatorname{grad} f$) and $g$ continuous with locally Lipschitz pull-backs $g\circ R_x$. Let $0<\tilde L$ and $L<\tilde L$, and let $\Omega\subseteq\mathcal M$ be open such that $f$ is $L$-retraction-smooth and retraction-convex in $\Omega$ and $g$ is retraction-convex in $\Omega$ (Assumption 3.3). Let $x\in\mathcal M$ and let $\eta^*_x\in T_x\mathcal M$ be a stationary point of
--   $$\ell_x(\eta)=\langle\operatorname{grad} f(x),\eta\rangle_x+\frac{\tilde L}{2}\|\eta\|_x^2+g(R_x(\eta))$$
--   (that is, $0\in\partial\ell_x(\eta^*_x)$) with $\ell_x(0)\ge\ell_x(\eta^*_x)$. If $x$ and $z=R_x(\eta^*_x)$ lie in $\Omega$, then for every $\xi_x\in T_x\mathcal M$ with $y:=R_x(\xi_x)\in\Omega$,
--   $$F(z)\le F(y)+\frac{\tilde L}{2}\left(\|\xi_x\|_x^2-\|\xi_x-\eta^*_x\|_x^2\right).$$
--
--   This is a Riemannian version of the three-point inequality for the Euclidean proximal gradient step (Beck–Teboulle, Lemma 2.3). It is the key estimate behind the $O(1/k)$ rate of Theorem 3.2, where it is applied with $x=x_k$ and $y$ an accumulation point.
--
--   **Formalization Note** Retraction-smoothness is Definition 3.1 as printed: (3.2) at every $x\in\Omega$ for the tangent vectors $\eta$ with $R_x(\eta)\in\Omega$ (only $\eta=\eta^*_x$ with $z\in\Omega$ is needed here). Retraction-convexity is that of the setting: (3.10) with $\zeta=\operatorname{grad}q_x(\xi)$ for $f$ and with every Clarke subgradient $\zeta\in\partial q_x(\xi)$ for $g$. The part "$\Omega\supseteq\Omega_{x_0}$" of Assumption 3.3 has no referent in this one-step statement (no $x_0$ occurs) and is omitted.
-- source:
--   Huang, Wei, Riemannian proximal gradient methods, arXiv:1909.06065v4, p. 11, Lemma 3.4

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting
import Definitions.Def_RiemOpt_FR_Setting
import Definitions.Def_RiemProxGrad_Global_Setting
import Definitions.Def_RiemProxGrad_Rate_Setting

open Bundle Manifold Filter
open scoped ContDiff

namespace RiemProxGrad.Rate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

/-- Lemma 3.4 (p. 11), the Riemannian three-point inequality. Let `η*_x` be a stationary point of
`ℓ_x` with `ℓ_x(0) ≥ ℓ_x(η*_x)`, and suppose `Ω` is open, `f` is `L`-retraction-smooth and
retraction-convex in `Ω` and `g` is retraction-convex in `Ω` (Assumption 3.3), with `0 < L̃` and `L < L̃`.
Retraction-smoothness is Definition 3.1 as printed: (3.2) for `x ∈ Ω` and `η` with `R_x(η) ∈ Ω`.
If `x` and `z = R_x(η*_x)` lie in `Ω`, then for every `ξ_x ∈ T_xM` with `y = R_x(ξ_x) ∈ Ω`,
`F(z) ≤ F(y) + (L̃/2)(‖ξ_x‖²_x − ‖ξ_x − η*_x‖²_x)`. -/
theorem lemma_3_4
    (f g : M → ℝ) (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (L Ltilde : ℝ) (Ω : Set M)
    (hP : StandingAssumptions f g grad R) (hLt : 0 < Ltilde) (hL : L < Ltilde)
    (hΩ : IsOpen Ω) (hfs : RiemProxGrad.Global.IsLRetractionSmooth R f grad L Ω)
    (hfc : IsRetractionConvexDiff f R Ω)
    (hgc : IsRetractionConvex g R Ω)
    (x : M) (ηs : TangentSpace 𝓘(ℝ, E) x)
    (hstat : (0 : TangentSpace 𝓘(ℝ, E) x) ∈ RiemProxGrad.Global.clarkeSubdiff (ell grad g R Ltilde x) ηs)
    (hdec : ell grad g R Ltilde x ηs ≤ ell grad g R Ltilde x 0)
    (hx : x ∈ Ω) (hz : R x ηs ∈ Ω) (ξ : TangentSpace 𝓘(ℝ, E) x) (hy : R x ξ ∈ Ω) :
    objective f g (R x ηs) ≤ objective f g (R x ξ) + Ltilde / 2 * (‖ξ‖ ^ 2 - ‖ξ - ηs‖ ^ 2) := by sorry

end RiemProxGrad.Rate
