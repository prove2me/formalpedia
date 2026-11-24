-- Prove2me | Theorems.Thm_RoughSurfaceScattering_tsp_halfplane_uniqueness
-- name    : RoughSurfaceScattering.tsp_halfplane_uniqueness
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T05:29:33.728494+00:00
-- url     : https://prove2.me/theorems/0018d985-fb59-4849-9ec9-9116acd5d4d4
-- title:
--   Scattered fields agreeing on $\Gamma_c$ above both interfaces agree in the half plane $x_2\ge c$
-- statement:
--   For $m=1,2$ let $(\Gamma_{f_m},k_{m,-},k_+,\mu_m)$ satisfy $f_m\in BC^{1,1}(\mathbb R)$, $k_+,k_{m,-},\mu_m>0$, $(\mu_m-1)(k_+^2-k_{m,-}^2\mu_m)\ge0$ and $k_+^2\ne k_{m,-}^2\mu_m$. Let $(u_{m,+},u_{m,-})$ solve the Transmission Scattering Problem for scatterer $m$ with arbitrary data $(g_{m,1},g_{m,2})$, and let $c>\max(f_1^+,f_2^+)$. If
--
--   $$u_{1,+}=u_{2,+}\quad\text{on the line }\Gamma_c=\{x_2=c\},$$
--
--   then
--
--   $$u_{1,+}(x)=u_{2,+}(x)\qquad\text{for all }x\text{ with }x_2\ge c .$$
--
--   Both scattered fields solve the Helmholtz equation with wave number $k_+$ in $U_c^+$, are bounded in every strip $c\le x_2\le H$, and satisfy the upward propagating radiation condition. Their difference therefore solves the homogeneous Dirichlet problem in the half plane $U_c^+$, whose only bounded radiating solution is zero. This is the second step of the continuation argument of [49, Theorem 4.1].
--
--   **Formalization Note** The two TSP solutions may have different data; only the properties of their upper fields are used.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, PDF p. 22, first paragraph ("Following the same procedure in the proof of [49, Theorem 4.1] ..."); half-plane step: uniqueness of the Dirichlet problem for the Helmholtz equation in U_c^+ under the upward propagating radiation condition for solutions bounded in strips (Chandler-Wilde and Zhang).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem tsp_halfplane_uniqueness (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1)
    (hf2 : IsBC1Alpha 1 f2) (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1)
    (hpar2 : ParamCond kp k2 μ2) (g11 g12 g21 g22 : ℝ → ℂ) (u1p u1m u2p u2m : R2 → ℂ)
    (hu1 : IsTSPSolution f1 kp k1 μ1 g11 g12 u1p u1m)
    (hu2 : IsTSPSolution f2 kp k2 μ2 g21 g22 u2p u2m)
    (c : ℝ) (hc1 : fsup f1 < c) (hc2 : fsup f2 < c)
    (hline : ∀ t : ℝ, u1p (pt t c) = u2p (pt t c)) :
    ∀ x : R2, c ≤ x 1 → u1p x = u2p x := by sorry

end RoughSurfaceScattering
