-- Prove2me | Theorems.Thm_RoughSurfaceScattering_tsp_exists
-- name    : RoughSurfaceScattering.tsp_exists
-- status  : Open
-- author  : @もち
-- created : 2026-11-26T15:13:28.37274+00:00
-- url     : https://prove2.me/theorems/316e1018-49eb-5446-b194-01103453caec
-- title:
--   Theorem 4.3 (existence): the TSP is solvable for data in $BC^{1,\alpha}(\Gamma)\times BC^{0,\alpha}(\Gamma)$
-- statement:
--   Let $f\in BC^{1,1}$, let the scatterer satisfy the conditions of Theorem 4.3 (`ParamCond`), and let $0<\alpha<1$. For every $g_1\in BC^{1,\alpha}(\Gamma)$ and $g_2\in BC^{0,\alpha}(\Gamma)$ the TSP has a solution $(u_+,u_-)$. The solution is
--
--   $$u_+=\mathcal D^+_{k_+,h_-}\varphi+\mathcal S^+_{k_+,h_-}\psi,\qquad u_-=\mu^{-1}\big(\mathcal D^-_{k_-,h_+}\varphi+\mathcal S^-_{k_-,h_+}\psi\big),$$
--
--   where $(\varphi,\psi)$ solves $M(\varphi,\psi)=(g_1,g_2)$ and $M$ is invertible on $[BC(\Gamma)]^2$.
--
--   **Formalization Note** The function classes are the platform's `IsBC1AlphaGam` and `IsBC0AlphaGam`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 4.3, pp. 16-17.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem tsp_exists (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ) (hpar : ParamCond kp km μ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (g1 g2 : ℝ → ℂ)
    (hg1 : IsBC1AlphaGam f α g1) (hg2 : IsBC0AlphaGam f α g2) :
    ∃ u : (R2 → ℂ) × (R2 → ℂ), IsTSPSolution f kp km μ g1 g2 u.1 u.2 := by sorry

end RoughSurfaceScattering
