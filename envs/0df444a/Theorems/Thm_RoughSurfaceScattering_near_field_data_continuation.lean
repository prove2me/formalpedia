-- Prove2me | Theorems.Thm_RoughSurfaceScattering_near_field_data_continuation
-- name    : RoughSurfaceScattering.near_field_data_continuation
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T03:28:13.616209+00:00
-- url     : https://prove2.me/theorems/695b6549-6b66-42e2-a274-7e1a6b3f98e8
-- title:
--   Theorem 6.1, step 0: near-field data on $\Gamma_{c,d}$ determine the scattered fields on $D_1^+\cap D_2^+$
-- statement:
--   For $m=1,2$ let $(\Gamma_{f_m},k_{m,-},k_+,\mu_m)$ be scatterers with a common upper wave number $k_+$: $f_m\in BC^{1,1}(\mathbb R)$, $k_+,k_{m,-},\mu_m>0$, $(\mu_m-1)(k_+^2-k_{m,-}^2\mu_m)\ge0$ and $k_+^2\ne k_{m,-}^2\mu_m$. Write $D_m^+=\{x:x_2>f_m(x_1)\}$ and, for $y\in D_m^+$, let $(u_{m,+}(\cdot,y),u_{m,-}(\cdot,y))$ solve the Transmission Scattering Problem (TSP) for scatterer $m$ with incident point source $u^i=\Phi_{k_+}(\cdot,y)$. Let $d>0$, let $c>f_1^+$ and $c>f_2^+$, and let $\Gamma_{c,d}=\{(x_1,c):|x_1|\le d\}$. If
--
--   $$u_{1,+}(x,y)=u_{2,+}(x,y)\qquad\text{for all }x,y\in\Gamma_{c,d},$$
--
--   then
--
--   $$u_{1,+}(x,y)=u_{2,+}(x,y)\qquad\text{for all }x,y\in D_1^+\cap D_2^+.$$
--
--   This is the first step of the proof of Theorem 6.1: measurements of the scattered field on one bounded segment, for sources on the same segment, already determine the scattered fields for all sources and receivers in the common upper region. The subsequent steps (determination of the interface, of $\mu$ and of $k_-$) only use the conclusion on $D_1^+\cap D_2^+$.
--
--   **Formalization Note** As in the formal statement of Theorem 6.1, the scattered fields are quantified over as families $y\mapsto(u_{m,+}(\cdot,y),u_{m,-}(\cdot,y))$ of TSP solutions indexed by the source point (unique by Theorem 3.3), with TSP data $g_1=-u^i|_\Gamma$, $g_2=-\partial_nu^i|_\Gamma$. The paper states $c>f^+$ for one interface; the segment is taken above both interfaces. The $C^{2,\lambda}$ regularity of Theorem 6.1 is not assumed, since this step does not use it.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, PDF p. 22, first paragraph of the proof ("Following the same procedure in the proof of [49, Theorem 4.1] ... for all x, y in D_1^+ ∩ D_2^+"); measurement segment Γ_{c,d}: Section 6, p. 22.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem near_field_data_continuation (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1) (hf2 : IsBC1Alpha 1 f2)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (c d : ℝ) (hd : 0 < d) (hc1 : fsup f1 < c) (hc2 : fsup f2 < c)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f1, IsTSPSolution f1 kp k1 μ1 (incData f1 (pointSource kp y)).1
      (incData f1 (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f2, IsTSPSolution f2 kp k2 μ2 (incData f2 (pointSource kp y)).1
      (incData f2 (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hdata : ∀ x ∈ measSeg c d, ∀ y ∈ measSeg c d, (U1 y).1 x = (U2 y).1 x) :
    ∀ x ∈ Dplus f1 ∩ Dplus f2, ∀ y ∈ Dplus f1 ∩ Dplus f2, (U1 y).1 x = (U2 y).1 x := by sorry

end RoughSurfaceScattering
