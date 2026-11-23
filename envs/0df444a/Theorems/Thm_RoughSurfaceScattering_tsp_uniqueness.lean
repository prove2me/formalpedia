-- Prove2me | Theorems.Thm_RoughSurfaceScattering_tsp_uniqueness
-- name    : RoughSurfaceScattering.tsp_uniqueness
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:55:23.542619+00:00
-- url     : https://prove2.me/theorems/1b0616fd-dae0-46a2-9fc1-4830369ff3e5
-- title:
--   Theorem 3.3: uniqueness for the transmission scattering problem
-- statement:
--   Let $f\in BC^{1,\alpha}(\mathbb R)$ with $0<\alpha\le1$ describe the interface $\Gamma$, and let $k_+,k_->0$ and $\mu>0$ satisfy
--
--   $$(\mu-1)(k_+^2-k_-^2\mu)\ge0,\qquad k_+^2\ne k_-^2\mu.$$
--
--   If $(u_+,u_-)$ solves the homogeneous Transmission Scattering Problem, i.e. the TSP with data $g_1=g_2=0$, then $u_+=0$ in $D^+$ and $u_-=0$ in $D^-$.
--
--   The condition covers $\mu=1$ with $k_+\ne k_-$, $\mu<1$ with $k_-^2\mu>k_+^2$, and $\mu>1$ with $k_-^2\mu<k_+^2$. No periodicity of $\Gamma$ is assumed. This is the uniqueness half of the well-posedness theory for real (lossless) wave numbers and a real transmission coefficient.
--
--   **Formalization Note** The positivity $k_\pm,\mu>0$ and $f\in BC^{1,\alpha}$ are the standing assumptions of Section 2. The growth condition (iii) of the TSP is used exactly as printed, $\sup_{D^\pm}|x_2|^\beta|u_\pm|<\infty$ with one $\beta$ for both fields. Since $|x_2|^\beta$ is not monotone in $\beta$, this shared exponent is a stricter requirement than a separate $\beta$ for each field, so the uniqueness statement covers fewer pairs than the per-field reading.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, claim c001; Section 3, Theorem 3.3, PDF p. 9 (TSP: Section 2, p. 6; radiation conditions: Definition 2.2, p. 5)

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem tsp_uniqueness (f : ℝ → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hf : IsBC1Alpha α f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (up um : R2 → ℂ)
    (hu : IsTSPSolution f kp km μ (fun _ => 0) (fun _ => 0) up um) :
    (∀ x ∈ Dplus f, up x = 0) ∧ ∀ x ∈ Dminus f, um x = 0 := by sorry

end RoughSurfaceScattering
