-- Prove2me | Theorems.Thm_RoughSurfaceScattering_phi_tsp_lower
-- name    : RoughSurfaceScattering.phi_tsp_lower
-- status  : Open
-- author  : @もち
-- created : 2026-11-25T06:40:32.983813+00:00
-- url     : https://prove2.me/theorems/f9167d8b-3c25-4c18-9e91-a5543e792bbe
-- title:
--   $(0,\,c\,\Phi_{k_-}(\cdot,z))$ is a TSP solution for $z\in D^+$
-- statement:
--   Let $z\in D^+$ and $c\in\mathbb C$. The pair $u_+=0$, $u_-=c\,\Phi_{k_-}(\cdot,z)$ solves the TSP with data
--
--   $$g_1=-c\,\Phi_{k_-}(\cdot,z)|_\Gamma,\qquad g_2=-\mu\,c\,\partial_n\Phi_{k_-}(\cdot,z)|_\Gamma .$$
--
--   Here $\Phi_{k_-}(\cdot,z)$ is smooth on $\overline{D^-}$, since $z$ is at positive distance from it, and solves the Helmholtz equation there. It and its gradient are bounded on the strip, and it satisfies the DPRC by Lemma 2.4 and Remark 2.5. The function $u_+=0$ satisfies the UPRC trivially.
--
--   **Formalization Note** The data are written as functions of the parameter $s$ of $\Gamma$, with the normal `normal f s`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Lemma 2.4 and Remark 2.5 (pp. 9-10), as used in the proof of Theorem 5.2 (p. 18).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem phi_tsp_lower (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ)
    (hpar : ParamCond kp km μ) (z : R2) (hz : z ∈ Dplus f) (c : ℂ) :
    IsTSPSolution f kp km μ (fun s => -(c * Phi km (gpt f s) z))
      (fun s => -((μ : ℂ) * (c * fderiv ℝ (fun x => Phi km x z) (gpt f s) (normal f s))))
      (fun _ => 0) (fun x => c * Phi km x z) := by sorry

end RoughSurfaceScattering
