-- Prove2me | Theorems.Thm_RoughSurfaceScattering_same_upper_boundary
-- name    : RoughSurfaceScattering.same_upper_boundary
-- status  : Proved
-- author  : @もち
-- created : 2026-11-27T02:16:04.120028+00:00
-- url     : https://prove2.me/theorems/b1fb3cba-cacf-4b6d-be4c-9efce134ecf9
-- title:
--   Equal upper fields give the ITP boundary conditions for the lower fields
-- statement:
--   Let $(u_{1,+},u_{1,-})$ and $(u_{2,+},u_{2,-})$ solve the TSP for $(\Gamma,k_1,k_+,\mu_1)$ and $(\Gamma,k_2,k_+,\mu_2)$ with the same data $(g_1,g_2)$, and suppose $u_{1,+}=u_{2,+}$ in $D^+$. Then $u_{1,-},u_{2,-}$ are $C^1$ up to $\Gamma$, and on $\Gamma$
--   $$u_{1,-}=u_{2,-},\qquad \frac{\mu_1}{\mu_2}\,\partial_nu_{1,-}=\partial_nu_{2,-}.$$
--   Indeed $u_{m,-}=u_{m,+}-g_1$ and $\mu_m\partial_nu_{m,-}=\partial_nu_{m,+}-g_2$, where $u_{1,+}$ and $u_{2,+}$ agree up to $\Gamma$ together with their gradients by continuity.
--
--   **Formalization Note** The gradients are given as functions $DV,DW$ with `IsC1On` on $\overline{D^-}$; on $D^-$ they are the derivatives.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 6.1, PDF pp. 22-24 ('Clearly, g_{1,j} = g_{2,j} = 0 on Γ̃ by the boundary conditions in the TSP', p. 23).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem same_upper_boundary (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp k1 k2 μ1 μ2 : ℝ)
    (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2) (g1 g2 : ℝ → ℂ)
    (u1p u1m u2p u2m : R2 → ℂ)
    (hu1 : IsTSPSolution f kp k1 μ1 g1 g2 u1p u1m) (hu2 : IsTSPSolution f kp k2 μ2 g1 g2 u2p u2m)
    (hagree : ∀ x ∈ Dplus f, u1p x = u2p x) :
    ∃ DV DW : R2 → (R2 →L[ℝ] ℂ), IsC1On (closure (Dminus f)) u1m DV ∧
      IsC1On (closure (Dminus f)) u2m DW ∧
      ∀ s, u1m (gpt f s) = u2m (gpt f s) ∧
        ((μ1 / μ2 : ℝ) : ℂ) * DV (gpt f s) (normal f s) = DW (gpt f s) (normal f s) := by sorry

end RoughSurfaceScattering
