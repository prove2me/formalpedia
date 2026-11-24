-- Prove2me | Theorems.Thm_RoughSurfaceScattering_lower_wavenumber_uniqueness
-- name    : RoughSurfaceScattering.lower_wavenumber_uniqueness
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T03:28:04.620803+00:00
-- url     : https://prove2.me/theorems/27a4a0f9-91b6-4b37-b198-91c4075c0775
-- title:
--   Theorem 6.1, step (iii): for a common interface and $\mu$, the scattered fields determine $k_-$
-- statement:
--   Let $f\in BC^{1,1}(\mathbb R)\cap C^{2,\lambda}(\mathbb R)$ with $\lambda\in(0,1]$ describe the interface $\Gamma$ and write $D^+=\{x:x_2>f(x_1)\}$. Let $k_+,\mu>0$ and let $k_{1,-},k_{2,-}>0$ be two lower wave numbers such that both scatterers $(\Gamma,k_{m,-},k_+,\mu)$, $m=1,2$, satisfy
--
--   $$(\mu-1)(k_+^2-k_{m,-}^2\mu)\ge0,\qquad k_+^2\ne k_{m,-}^2\mu .$$
--
--   For $y\in D^+$ let $(u_{m,+}(\cdot,y),u_{m,-}(\cdot,y))$ solve the Transmission Scattering Problem for $(\Gamma,k_{m,-},k_+,\mu)$ with incident point source $\Phi_{k_+}(\cdot,y)$. If
--
--   $$u_{1,+}(x,y)=u_{2,+}(x,y)\qquad\text{for all }x,y\in D^+,$$
--
--   then $k_{1,-}=k_{2,-}$.
--
--   This is part (iii) of the proof of Theorem 6.1: once the interface and the transmission coefficient have been identified, the scattered fields above the interface also determine the wave number of the lower medium.
--
--   **Formalization Note** The scattered fields are quantified over as families of TSP solutions indexed by the source point, unique by Theorem 3.3, as in the formal statement of Theorem 6.1.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, part (iii), PDF p. 25 ("Finally we show k_{1,-} = k_{2,-}").

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem lower_wavenumber_uniqueness (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1) (hf' : IsC2Lambda lam f)
    (kp k1 k2 μ : ℝ) (hpar1 : ParamCond kp k1 μ) (hpar2 : ParamCond kp k2 μ)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f, IsTSPSolution f kp k1 μ (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f, IsTSPSolution f kp k2 μ (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f, ∀ y ∈ Dplus f, (U1 y).1 x = (U2 y).1 x) :
    k1 = k2 := by sorry

end RoughSurfaceScattering
