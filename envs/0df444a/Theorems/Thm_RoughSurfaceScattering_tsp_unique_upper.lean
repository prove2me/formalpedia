-- Prove2me | Theorems.Thm_RoughSurfaceScattering_tsp_unique_upper
-- name    : RoughSurfaceScattering.tsp_unique_upper
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T03:08:29.873602+00:00
-- url     : https://prove2.me/theorems/47d82754-d68a-4dc3-aaf4-ba9f1e7d61e6
-- title:
--   Uniqueness of the transmission scattering problem (upper field)
-- statement:
--   Under (2.2), two TSP solutions $(u_+,u_-)$ and $(v_+,v_-)$ with the same data $(g_1,g_2)$ have $u_+=v_+$ in $D^+$.
--   This is Theorem 3.3 applied to the difference, which solves the homogeneous TSP: the Rellich-type identity together with the UPRC/DPRC conditions gives $u_\pm=v_\pm$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 3.3 (uniqueness) and Theorem 4.3 / Section 4 (integral-equation solution); used in the proof of Theorem 6.1 (Theorem 3.3: the TSP has at most one solution).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem tsp_unique_upper (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ)
    (hpar : ParamCond kp km μ) (g1 g2 : ℝ → ℂ) (up um vp vm : R2 → ℂ)
    (hu : IsTSPSolution f kp km μ g1 g2 up um) (hv : IsTSPSolution f kp km μ g1 g2 vp vm) :
    ∀ x ∈ Dplus f, up x = vp x := by sorry

end RoughSurfaceScattering
