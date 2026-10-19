-- Prove2me | Theorems.Thm_RelPartMech_poisson_velocities
-- name    : RelPartMech.poisson_velocities
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T23:11:19.662406+00:00
-- url     : https://prove2.me/theorems/25c4aa15-b5ed-4f12-8af4-6e0f83bc44d1
-- title:
--   Poisson bracket of velocities
-- statement:
--   With $u^\alpha=\frac1m g^{\alpha\beta}(p_\beta-eA_\beta)$, smooth metric $g$, smooth potential $A$ and $m\neq0$,
--
--   $$
--   \{u^\alpha,u^\beta\} = \frac1{m^2}\Big(G^{\alpha\beta\gamma}\,m\,g_{\gamma\delta}u^\delta + e\,F^{\alpha\beta}\Big),
--   $$
--
--   where $G^{\alpha\beta\gamma}$ and $F^{\alpha\beta}$ are the raised symbols of eq. (11). The non-commutativity of the velocities combines the force tensor with the symbol $G$.
-- source:
--   G. Carcassi, C. A. Aidala, "Relativity and Particle Mechanics" (note, uploaded PDF), p. 6, eq. (13), third block (final line)

import Mathlib
import Definitions.Def_RelPartMech_coordinates

open scoped ContDiff

namespace RelPartMech

theorem poisson_velocities {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α)) (e m : ℝ) (hm : m ≠ 0)
    (α β : Fin n) (x p : Coord n) :
    poisson (velocity g A e m α) (velocity g A e m β) x p =
      (1 / m ^ 2) * (∑ γ, ∑ δ, gSymbolUp g α β γ x * m * g x γ δ * velocity g A e m δ x p
        + e * forceTensorUp g A α β x) := by sorry

end RelPartMech
