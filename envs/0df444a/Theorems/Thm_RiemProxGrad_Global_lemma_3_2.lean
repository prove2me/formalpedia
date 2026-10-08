-- Prove2me | Theorems.Thm_RiemProxGrad_Global_lemma_3_2
-- name    : RiemProxGrad.Global.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:33.502485+00:00
-- url     : https://prove2.me/theorems/3572e9e0-0f3d-478f-be3b-5db789937c26
-- title:
--   Lemma 3.2 — $\|\xi_y-\mathcal T^{-\sharp}_{\eta_x}\xi_x\|_y\to0$ as $\eta_x\to0$, $y=R_x(\eta_x)$
-- statement:
--   Let $\mathcal M$ be a finite-dimensional manifold with a smooth Riemannian metric, $R$ a smooth retraction, and $\mathcal T$ the vector transport by differentiated retraction, $\mathcal T_{\eta_x}\zeta_x = \frac{d}{dt}R_x(\eta_x + t\zeta_x)\big|_{t=0}$. Write $\mathcal T^{-\sharp}_{\eta_x}$ for the adjoint of the inverse of $\mathcal T_{\eta_x}$, a map $T_x\mathcal M\to T_y\mathcal M$ with $y = R_x(\eta_x)$. Let $\xi$ be a continuous vector field on $\mathcal M$. Then
--   $$\lim_{\eta_x\to 0}\ \big\|\xi_y - \mathcal T^{-\sharp}_{\eta_x}\xi_x\big\|_y = 0,\qquad y = R_x(\eta_x),$$
--   where the limit is taken on the tangent bundle: as $(x,\eta_x)\to(\bar x, 0_{\bar x})$ in $T\mathcal M$, for every $\bar x\in\mathcal M$.
--
--   The lemma lets the proof of Theorem 3.1 compare the gradient at the new iterate $x_{k+1} = R_{x_k}(\eta^*_{x_k})$ with the transported gradient at $x_k$ when the step is small, along a subsequence whose base points $x_{k_j}$ move.
--
--   **Formalization Note** The limit is over the tangent bundle (the proof shows that $h : T\mathcal M\to T\mathcal M$, $\eta_x\mapsto\xi_y - \mathcal T^{-\sharp}_{\eta_x}\xi_x$, is continuous with $h(0_x) = 0$), which is the form Theorem 3.1 uses; the fixed-$x$ limit is a special case. Continuity of $\xi$ is continuity of $x\mapsto(x,\xi_x)$ into $T\mathcal M$. Mathlib's `ContinuousLinearMap.inverse` is $0$ where $\mathcal T_{\eta_x}$ is not invertible, which does not affect the limit since $\mathcal T_{0_x} = \mathrm{id}$.
-- source:
--   Huang, Wei, Riemannian proximal gradient methods, arXiv:1909.06065v4, p. 8, Lemma 3.2

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting
import Definitions.Def_RiemOpt_FR_Setting
import Definitions.Def_RiemProxGrad_Global_Setting

open Bundle Manifold Filter Topology
open scoped ContDiff

namespace RiemProxGrad.Global

/-- Lemma 3.2 (Huang–Wei, arXiv:1909.06065v4, p. 8): for a continuous vector field `ξ`,
`‖ξ_y − T^{−♯}_{η_x} ξ_x‖_y → 0` as `η_x → 0`, where `y = R_x(η_x)` and `T` is the vector transport
by differentiated retraction. The limit is taken on the tangent bundle: `(x, η_x) → (x̄, 0_{x̄})`. -/
theorem lemma_3_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    {R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M} (hR : IsSmoothRetraction R)
    {ξ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hξ : Continuous (fun x : M => (⟨x, ξ x⟩ : TangentBundle 𝓘(ℝ, E) M))) (xbar : M) :
    Tendsto (fun p : TangentBundle 𝓘(ℝ, E) M =>
        ‖ξ (R p.1 p.2) - transportInvAdj R p.1 p.2 (ξ p.1)‖)
      (𝓝 (⟨xbar, 0⟩ : TangentBundle 𝓘(ℝ, E) M)) (𝓝 0) := by sorry

end RiemProxGrad.Global
