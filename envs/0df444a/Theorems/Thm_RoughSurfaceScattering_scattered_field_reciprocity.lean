-- Prove2me | Theorems.Thm_RoughSurfaceScattering_scattered_field_reciprocity
-- name    : RoughSurfaceScattering.scattered_field_reciprocity
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T04:42:48.094905+00:00
-- url     : https://prove2.me/theorems/9d456880-85d3-4a60-a934-33cadf06ed5a
-- title:
--   Reciprocity of the point-source scattered field: $u_+(x,y)=u_+(y,x)$
-- statement:
--   Let $f\in BC^{1,1}(\mathbb R)$ describe the interface $\Gamma$ with upper region $D^+$, and let $k_\pm,\mu>0$ satisfy $(\mu-1)(k_+^2-k_-^2\mu)\ge0$ and $k_+^2\ne k_-^2\mu$. For $y\in D^+$ let $(u_+(\cdot,y),u_-(\cdot,y))$ solve the Transmission Scattering Problem with incident point source $\Phi_{k_+}(\cdot,y)$. Then
--
--   $$u_+(x,y)=u_+(y,x)\qquad\text{for all }x,y\in D^+ .$$
--
--   This is the reciprocity relation for the scattered field of the transmission problem. It follows from Green's second identity applied to the total fields of the two point sources, using the transmission conditions on $\Gamma$ and the radiation conditions; uniqueness (Theorem 3.3) identifies the solutions. In the proof of Theorem 6.1 it allows the roles of sources and receivers in the near-field data to be exchanged.
--
--   **Formalization Note** The scattered fields are quantified over as a family of TSP solutions indexed by the source point, as in Theorem 6.1.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, PDF p. 22, first paragraph ("Following the same procedure in the proof of [49, Theorem 4.1] ..."); the reciprocity step of the procedure of [49, Theorem 4.1].

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem scattered_field_reciprocity (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ)
    (hpar : ParamCond kp km μ) (U : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU : ∀ y ∈ Dplus f, IsTSPSolution f kp km μ (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U y).1 (U y).2) :
    ∀ x ∈ Dplus f, ∀ y ∈ Dplus f, (U y).1 x = (U x).1 y := by sorry

end RoughSurfaceScattering
