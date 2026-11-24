-- Prove2me | Theorems.Thm_RoughSurfaceScattering_mu_itp_bound
-- name    : RoughSurfaceScattering.mu_itp_bound
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T03:52:48.730597+00:00
-- url     : https://prove2.me/theorems/4f83d1c4-9722-438b-8ae1-f14dc1e776b3
-- title:
--   Theorem 6.1 (i): interior transmission bound for the transmitted fields when $\mu_1\ne\mu_2$
-- statement:
--   Let $f\in BC^{1,1}(\mathbb R)\cap C^{2,\lambda}(\mathbb R)$ with $\lambda\in(0,1]$ describe the interface $\Gamma$, with $D^\pm$ the regions above and below it and $n$ the unit normal pointing into $D^-$. For $m=1,2$ let $(\Gamma,k_{m,-},k_+,\mu_m)$ satisfy $k_+,k_{m,-},\mu_m>0$, $(\mu_m-1)(k_+^2-k_{m,-}^2\mu_m)\ge0$ and $k_+^2\ne k_{m,-}^2\mu_m$, and assume
--
--   $$\mu_1\ne\mu_2 .$$
--
--   Suppose the point-source scattered fields agree: $u_{1,+}(x,y)=u_{2,+}(x,y)$ for all $x,y\in D^+$. Fix $x_0\in\Gamma$ and put $x_j=x_0-\frac\delta j\,n(x_0)$.
--
--   Then there is $\delta_1>0$ such that for every $\delta\in(0,\delta_1)$ there are a bounded $C^{2,\lambda}$ domain $D_0$ with $B_{2\delta}(x_0)\cap D^-\subseteq D_0\subseteq D^-$ and a constant $C$ with
--
--   $$\big\|u_{1,-}(\cdot,x_j)\big\|_{H^1(D_0)}\le C\qquad(j\ge1).$$
--
--   The pair $(u_{1,-}(\cdot,x_j),u_{2,-}(\cdot,x_j))$ solves the interior transmission problem (6.1) in $D_0$ with $\rho=\mu_1/\mu_2\ne1$, whose boundary data vanish on $\partial D_0\cap\Gamma$. The a priori estimate of [9, Theorem 6.7], with the $L^2$ and boundary bounds supplied by Theorem 5.2, gives this bound uniformly in $j$. It contradicts the $H^1$ singularity of $u_{1,-}(\cdot,x_j)$ described in Theorem 5.2.
--
--   **Formalization Note** $x_0=(s_0,f(s_0))$ and $n(x_0)$ is `normal f s0`. The scattered fields are quantified over as families of TSP solutions indexed by the source point, as in Theorem 6.1.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, part (i), PDF pp. 23–24 (interior transmission problem (6.1) with (V_j, W_j) = (u_{1,-}^{(j)}, u_{2,-}^{(j)}), ρ = µ_1/µ_2, estimate (6.2) from [9, Theorem 6.7]: "‖u_{1,-}^{(j)}‖_{H^1(D_0)} ≤ C uniformly for j ∈ N").

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem mu_itp_bound (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1) (hf' : IsC2Lambda lam f)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (hμ : μ1 ≠ μ2)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f, IsTSPSolution f kp k1 μ1 (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f, IsTSPSolution f kp k2 μ2 (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f, ∀ y ∈ Dplus f, (U1 y).1 x = (U2 y).1 x) (s0 : ℝ) :
    ∃ δ1 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ1 →
      ∃ D0 : Set R2, IsC2LambdaDomain lam D0 ∧
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 ∧ D0 ⊆ Dminus f ∧
        ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
          h1Norm D0 (U1 (gpt f s0 - (δ / (j : ℝ)) • normal f s0)).2 ≤ ENNReal.ofReal C := by sorry

end RoughSurfaceScattering
