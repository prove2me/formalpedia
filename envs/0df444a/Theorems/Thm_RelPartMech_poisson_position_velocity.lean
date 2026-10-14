-- Prove2me | Theorems.Thm_RelPartMech_poisson_position_velocity
-- name    : RelPartMech.poisson_position_velocity
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:10:46.504651+00:00
-- url     : https://prove2.me/theorems/eabc3359-7f58-40a3-97b7-d75be4fe1b61
-- title:
--   $\{x^\alpha,u^\beta\}=g^{\alpha\beta}/m$
-- statement:
--   With velocity $u^\beta = \frac1m g^{\beta\gamma}(p_\gamma-eA_\gamma)$ (so that $p_\alpha = m g_{\alpha\beta}u^\beta+eA_\alpha$), smooth $g$, $A$ and $m\ne0$,
--
--   $$
--   \{x^\alpha,u^\beta\} = \frac1m\, g^{\alpha\beta}.
--   $$
-- source:
--   G. Carcassi, C. A. Aidala, "Relativity and Particle Mechanics" (note, uploaded PDF), p. 6, eq. (13), second block

import Mathlib
import Definitions.Def_RelPartMech_coordinates

open scoped ContDiff

namespace RelPartMech

theorem poisson_position_velocity {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α)) (e m : ℝ) (hm : m ≠ 0)
    (α β : Fin n) (x p : Coord n) :
    poisson (posFn α) (velocity g A e m β) x p = (1 / m) * ginv g x α β := by sorry

end RelPartMech
