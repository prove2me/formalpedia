-- Prove2me | Theorems.Thm_RelPartMech_gSymbolUp_eq
-- name    : RelPartMech.gSymbolUp_eq
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:08:42.967391+00:00
-- url     : https://prove2.me/theorems/de18c3b5-f139-43e6-8419-fd39265fef73
-- title:
--   Raised form of $G$: $G^{\alpha\beta\gamma}=\partial^\beta g^{\alpha\gamma}-\partial^\alpha g^{\beta\gamma}$
-- statement:
--   For a smooth metric $g$, raise all indices of $G$: $G^{\alpha\beta\gamma}=g^{\alpha\delta}g^{\beta\epsilon}g^{\gamma\zeta}G_{\delta\epsilon\zeta}$, and write $\partial^\alpha=g^{\alpha\beta}\partial_\beta$. Then
--
--   $$
--   G^{\alpha\beta\gamma} = \partial^\beta g^{\alpha\gamma}-\partial^\alpha g^{\beta\gamma}.
--   $$
-- source:
--   G. Carcassi, C. A. Aidala, "Relativity and Particle Mechanics" (note, uploaded PDF), p. 5, eq. (11), first block

import Mathlib
import Definitions.Def_RelPartMech_coordinates

open scoped ContDiff

namespace RelPartMech

theorem gSymbolUp_eq {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (α β γ : Fin n) (x : Coord n) :
    gSymbolUp g α β γ x =
      pdUp g β (fun y => ginv g y α γ) x - pdUp g α (fun y => ginv g y β γ) x := by sorry

end RelPartMech
