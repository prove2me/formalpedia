-- Prove2me | Theorems.Thm_QuantileSPQO_Rate_eq_4
-- name    : QuantileSPQO.Rate.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:46.103434+00:00
-- url     : https://prove2.me/theorems/a456122a-3dca-4583-8e76-d5f242c3ce69
-- title:
--   Display (4) — the quantile gradient ∇q(θ) = −∇_θF(y;θ)|_{y=q} / f(q;θ)
-- statement:
--   Let $Y(\theta)$ be a continuous random variable with c.d.f. $F(y;\theta)$ and density $f(y;\theta)=\partial F/\partial y$ for every $\theta\in\mathbb R^d$, and let $q(\theta)$ be its $\varphi$-quantile, $F(q(\theta);\theta)=\varphi$ for all $\theta$. Fix $\theta$ such that $q$ is differentiable at $\theta$, the map $(y,\theta')\mapsto F(y;\theta')$ is differentiable at $(q(\theta),\theta)$, and $f(q(\theta);\theta)\ne0$. Then
--   $$
--   \nabla_\theta q(\theta)=-\frac{\nabla_\theta F(y;\theta)\big|_{y=q(\theta)}}{f(q(\theta);\theta)}.
--   $$
--
--   This relationship (cited by the paper from Fu et al. 2009) is what the gradient recursion (21) of SPQO tracks, and it is used in the proof of Lemma 5.
--
--   **Formalization Note** The paper states (4) "under appropriate smoothness conditions"; they are made explicit as the differentiability of $q$ at $\theta$, joint differentiability of $F$ at $(q(\theta),\theta)$ and $f(q(\theta);\theta)\ne0$. The quantile model is the one of the Setting file; its uniqueness clause on $\Theta$ is not used here.
-- source:
--   Hu, Song and Fu, Quantile Optimization via Multiple Timescale Local Search for Black-box Functions, arXiv:2308.07607v1, p. 3, display (4)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_QuantileSPQO_Rate_Setting

open Filter Topology

namespace QuantileSPQO.Rate

theorem eq_4 {d : ℕ} (M : Model d) (Θ : Set (E d)) (hM : IsQuantileModel M Θ) (θ : E d)
    (hq : DifferentiableAt ℝ M.qf θ) (hF : DifferentiableAt ℝ (cdfU M) (M.qf θ, θ))
    (hf : M.dens (M.qf θ) θ ≠ 0) :
    gradient M.qf θ = -(M.dens (M.qf θ) θ)⁻¹ • gradθ M (M.qf θ) θ := by sorry

end QuantileSPQO.Rate
