-- Prove2me | Theorems.Thm_RoughSurfaceScattering_tsp_upper_trace_representation
-- name    : RoughSurfaceScattering.tsp_upper_trace_representation
-- status  : Open
-- author  : @もち
-- created : 2026-11-26T15:11:16.443223+00:00
-- url     : https://prove2.me/theorems/0c915ec9-5c96-41ae-8de7-e37f8cac5716
-- title:
--   The scattered field above $\Gamma_h$ is the double-layer potential of its own trace on $\Gamma_h$ ($h>f^+$)
-- statement:
--   Let $(u_+,u_-)$ be a solution of the TSP and let $h>f^+$. Then
--
--   $$u_+(x)=2\int_{\mathbb R}\frac{\partial\Phi_{k_+}(x,y)}{\partial y_2}\Big|_{y=(t,h)}\,u_+(t,h)\,dt\qquad\text{for all }x\in U_h^+ .$$
--
--   Indeed $u_+\in C^2(U_H^+)$ solves the Helmholtz equation for any $H\in(f^+,h)$, is bounded on the strips $U_H^+\setminus U_a^+$ (the $BC^1$ condition near $\Gamma$ and the UPRC representation above), and satisfies the UPRC. By Lemma 2.4 ((i)⇒(iv)), $u_+$ satisfies (2.3) at every height $h>H$ with density $\varphi=u_+|_{\Gamma_h}$.
--
--   **Formalization Note** The kernel is `dPhi_dy2` as in `IsUPRC`. Points of $\Gamma_h$ are `pt t h`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Lemma 2.4 (equivalence (i)⇔(iv), from [22] Chandler-Wilde and Zhang), pp. 9-10.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem tsp_upper_trace_representation (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ)
    (hpar : ParamCond kp km μ) (g1 g2 : ℝ → ℂ) (up um : R2 → ℂ)
    (hu : IsTSPSolution f kp km μ g1 g2 up um) (h : ℝ) (hh : fsup f < h) :
    ∀ x ∈ Uplus h, up x = 2 * ∫ t, dPhi_dy2 kp x (pt t h) * up (pt t h) := by sorry

end RoughSurfaceScattering
