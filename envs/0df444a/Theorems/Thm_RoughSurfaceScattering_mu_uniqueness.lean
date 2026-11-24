-- Prove2me | Theorems.Thm_RoughSurfaceScattering_mu_uniqueness
-- name    : RoughSurfaceScattering.mu_uniqueness
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T03:52:50.261902+00:00
-- url     : https://prove2.me/theorems/457e0a93-3461-44c2-b332-45a101588d1f
-- title:
--   Theorem 6.1 (i)–(ii): for a common interface, the scattered fields determine $\mu$
-- statement:
--   Let $f\in BC^{1,1}(\mathbb R)\cap C^{2,\lambda}(\mathbb R)$ with $\lambda\in(0,1]$ describe the interface $\Gamma$ and write $D^+=\{x:x_2>f(x_1)\}$. For $m=1,2$ let $(\Gamma,k_{m,-},k_+,\mu_m)$ be scatterers with the same interface and the same upper wave number, with $k_+,k_{m,-},\mu_m>0$, $(\mu_m-1)(k_+^2-k_{m,-}^2\mu_m)\ge0$ and $k_+^2\ne k_{m,-}^2\mu_m$. For $y\in D^+$ let $(u_{m,+}(\cdot,y),u_{m,-}(\cdot,y))$ solve the Transmission Scattering Problem for scatterer $m$ with incident point source $\Phi_{k_+}(\cdot,y)$. If
--
--   $$u_{1,+}(x,y)=u_{2,+}(x,y)\qquad\text{for all }x,y\in D^+,$$
--
--   then $\mu_1=\mu_2$.
--
--   This is the identification of the transmission coefficient in parts (i) and (ii) of the proof of Theorem 6.1, once the interface is known.
--
--   **Formalization Note** The scattered fields are quantified over as families of TSP solutions indexed by the source point, as in Theorem 6.1. The lower wave numbers $k_{1,-},k_{2,-}$ may differ.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, part (i), PDF pp. 23–24 ("Next we show µ_1 = µ_2 ... Hence, µ_1 = µ_2"), and part (ii), PDF p. 25 ("following similarly as the arguments in (i), we can obtain that µ_2 = µ_1 = 1").

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem mu_uniqueness (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1) (hf' : IsC2Lambda lam f)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f, IsTSPSolution f kp k1 μ1 (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f, IsTSPSolution f kp k2 μ2 (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f, ∀ y ∈ Dplus f, (U1 y).1 x = (U2 y).1 x) :
    μ1 = μ2 := by sorry

end RoughSurfaceScattering
