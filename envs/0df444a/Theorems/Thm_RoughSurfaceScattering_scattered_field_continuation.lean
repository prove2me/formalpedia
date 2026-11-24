-- Prove2me | Theorems.Thm_RoughSurfaceScattering_scattered_field_continuation
-- name    : RoughSurfaceScattering.scattered_field_continuation
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T04:42:41.017794+00:00
-- url     : https://prove2.me/theorems/80284020-39a6-4968-8a96-1bae04eec22a
-- title:
--   Scattered fields of one source agreeing on $\Gamma_{c,d}$ agree on $D_1^+\cap D_2^+$
-- statement:
--   For $m=1,2$ let $(\Gamma_{f_m},k_{m,-},k_+,\mu_m)$ be scatterers with a common upper wave number: $f_m\in BC^{1,1}(\mathbb R)$, $k_+,k_{m,-},\mu_m>0$, $(\mu_m-1)(k_+^2-k_{m,-}^2\mu_m)\ge0$ and $k_+^2\ne k_{m,-}^2\mu_m$. Let $y\in D_1^+\cap D_2^+$, and let $(u_{m,+},u_{m,-})$ solve the TSP for scatterer $m$ with incident point source $\Phi_{k_+}(\cdot,y)$. Let $d>0$, let $c>\max(f_1^+,f_2^+)$ and $\Gamma_{c,d}=\{(x_1,c):|x_1|\le d\}$. If
--
--   $$u_{1,+}=u_{2,+}\quad\text{on }\Gamma_{c,d},$$
--
--   then
--
--   $$u_{1,+}=u_{2,+}\quad\text{in }D_1^+\cap D_2^+ .$$
--
--   The difference $w=u_{1,+}-u_{2,+}$ solves the Helmholtz equation with wave number $k_+$ in the connected open set $D_1^+\cap D_2^+$, so it is real analytic there. Vanishing on the segment $\Gamma_{c,d}$ therefore forces $w=0$ on the whole line $\Gamma_c$. The uniqueness of the Dirichlet problem in the half plane $U_c^+$ under the upward propagating radiation condition then gives $w=0$ in $U_c^+$, and unique continuation extends this to $D_1^+\cap D_2^+$. This is the continuation step of the procedure of [49, Theorem 4.1] invoked in the proof of Theorem 6.1.
--
--   **Formalization Note** Only the scattered fields $u_{m,+}$ of one fixed source $y$ enter. The segment is taken above both interfaces.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, PDF p. 22, first paragraph ("Following the same procedure in the proof of [49, Theorem 4.1] ..."); the analytic-continuation step of the procedure of [49, Theorem 4.1] (analyticity on Γ_c, uniqueness of the Dirichlet problem in U_c^+ under the UPRC, unique continuation).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem scattered_field_continuation (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1)
    (hf2 : IsBC1Alpha 1 f2) (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1)
    (hpar2 : ParamCond kp k2 μ2) (y : R2) (hy : y ∈ Dplus f1 ∩ Dplus f2)
    (u1p u1m u2p u2m : R2 → ℂ)
    (hu1 : IsTSPSolution f1 kp k1 μ1 (incData f1 (pointSource kp y)).1
      (incData f1 (pointSource kp y)).2 u1p u1m)
    (hu2 : IsTSPSolution f2 kp k2 μ2 (incData f2 (pointSource kp y)).1
      (incData f2 (pointSource kp y)).2 u2p u2m)
    (c d : ℝ) (hd : 0 < d) (hc1 : fsup f1 < c) (hc2 : fsup f2 < c)
    (hseg : ∀ x ∈ measSeg c d, u1p x = u2p x) :
    ∀ x ∈ Dplus f1 ∩ Dplus f2, u1p x = u2p x := by sorry

end RoughSurfaceScattering
