-- Prove2me | Theorems.Thm_RoughSurfaceScattering_interface_itp_bound_point
-- name    : RoughSurfaceScattering.interface_itp_bound_point
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T04:01:14.10494+00:00
-- url     : https://prove2.me/theorems/6a05b942-69ba-4a1d-9b5c-14846b33eb33
-- title:
--   Theorem 6.1 (i): interior transmission bound (6.2) when $x_0\in\Gamma_{f_1}\setminus\Gamma_{f_2}$ and $\mu_1\ne1$
-- statement:
--   For $m=1,2$ let $(\Gamma_{f_m},k_{m,-},k_+,\mu_m)$ be scatterers with a common upper wave number $k_+$, each satisfying the hypotheses of Theorem 5.2: $f_m\in BC^{1,1}(\mathbb R)\cap C^{2,\lambda_m}(\mathbb R)$ with $\lambda_m\in(0,1]$, $k_+,k_{m,-},\mu_m>0$, $(\mu_m-1)(k_+^2-k_{m,-}^2\mu_m)\ge0$ and $k_+^2\ne k_{m,-}^2\mu_m$. Write $D_m^\pm$ for the regions above and below $\Gamma_{f_m}$ and, for $y\in D_m^+$, let $(u_{m,+}(\cdot,y),u_{m,-}(\cdot,y))$ solve the TSP for scatterer $m$ with incident point source $\Phi_{k_+}(\cdot,y)$. Suppose
--
--   $$u_{1,+}(x,y)=u_{2,+}(x,y)\qquad\text{for all }x,y\in D_1^+\cap D_2^+,$$
--
--   and let $x_0=(s_0,f_1(s_0))\in\Gamma_{f_1}$ be a point with $f_1(s_0)>f_2(s_0)$, so that $x_0\in D_2^+$. With $n(x_0)$ the unit normal of $\Gamma_{f_1}$ at $x_0$ pointing into $D_1^-$, put $x_j=x_0-\frac\delta j\,n(x_0)$. Assume moreover
--
--   $$\mu_1\ne1 .$$
--
--   Then there is $\delta_1>0$ such that for every $\delta\in(0,\delta_1)$:
--
--   1. $x_j\in D_2^+$ for all $j\ge1$;
--   2. there is a bounded $C^{2,\lambda_1}$ domain $D_0$ with $B_{2\delta}(x_0)\cap D_1^-\subseteq D_0\subseteq D_1^-\cap D_2^+$ such that, if $\sup_{j\ge1}\|u_{1,-}(\cdot,x_j)\|_{L^2(D_0)}<\infty$, then the total field $u_{2,j}=\Phi_{k_+}(\cdot,x_j)+u_{2,+}(\cdot,x_j)$ and the scattered field $u_{2,+}(\cdot,x_j)$ satisfy, for some $C$ independent of $j$,
--   $$\|u_{2,j}\|_{H^1(D_0)}\le C,\qquad\|u_{2,+}(\cdot,x_j)\|_{H^1(D_0)}\le C\qquad(j\ge1).$$
--
--   The pair $(u_{1,-}(\cdot,x_j),u_{2,j})$ solves the interior transmission problem (6.1) in $D_0$ with $\rho=\mu_1\ne1$ and boundary data vanishing on $\partial D_0\cap\Gamma_{f_1}$. The a priori estimate (6.2) turns the $L^2$ bounds into the $H^1$ bound. The bound for $u_{2,+}$ comes from Theorem 4.3, since $D_0$ stays away from $\Gamma_{f_2}$.
--
--   **Formalization Note** The $L^2$ bound on $u_{1,-}(\cdot,x_j)$, which the paper derives from Theorem 5.2, is a hypothesis of item 2. The scattered fields are quantified over as families of TSP solutions indexed by the source point, as in Theorem 6.1.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, part (i), PDF pp. 22–23: interior transmission problem (6.1) with (V_j, W_j) = (u_{1,-}^{(j)}, u_{2,j}), ρ = µ_1, estimate (6.2) from [9, Theorem 6.7], the bound ‖u_{2,+}^{(j)}‖_{H^1(D_0)} ≤ C from Theorem 4.3, and "‖u_{2,j}‖_{H^1(D_0)} ≤ C uniformly for j ∈ N".

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem interface_itp_bound_point (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1) (hf2 : IsBC1Alpha 1 f2)
    (lam1 lam2 : ℝ) (hlam1 : 0 < lam1 ∧ lam1 ≤ 1) (hlam2 : 0 < lam2 ∧ lam2 ≤ 1)
    (hf1' : IsC2Lambda lam1 f1) (hf2' : IsC2Lambda lam2 f2)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (hμ1 : μ1 ≠ 1)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f1, IsTSPSolution f1 kp k1 μ1 (incData f1 (pointSource kp y)).1
      (incData f1 (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f2, IsTSPSolution f2 kp k2 μ2 (incData f2 (pointSource kp y)).1
      (incData f2 (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f1 ∩ Dplus f2, ∀ y ∈ Dplus f1 ∩ Dplus f2, (U1 y).1 x = (U2 y).1 x)
    (s0 : ℝ) (hs : f2 s0 < f1 s0) :
    ∃ δ1 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ1 →
      (∀ j : ℕ, 1 ≤ j → (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0) ∈ Dplus f2) ∧
      ∃ D0 : Set R2, IsC2LambdaDomain lam1 D0 ∧
        Metric.ball (gpt f1 s0) (2 * δ) ∩ Dminus f1 ⊆ D0 ∧ D0 ⊆ Dminus f1 ∧ D0 ⊆ Dplus f2 ∧
        ((∃ C : ℝ, ∀ j : ℕ, 1 ≤ j → l2Norm D0 (U1 (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)).2 ≤ ENNReal.ofReal C) →
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
            h1Norm D0 (fun x => pointSource kp (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0) x + (U2 (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)).1 x) ≤ ENNReal.ofReal C ∧
            h1Norm D0 (U2 (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0)).1 ≤ ENNReal.ofReal C) := by sorry

end RoughSurfaceScattering
