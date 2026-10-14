-- Prove2me | Theorems.Thm_RelPartMech_gSymbol_eq_christoffel_diff
-- name    : RelPartMech.gSymbol_eq_christoffel_diff
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:08:17.605575+00:00
-- url     : https://prove2.me/theorems/61035cbe-0c8e-4fe0-9d5f-fd472240dc75
-- title:
--   $G_{\alpha\beta\gamma}=\Gamma_{\beta\alpha\gamma}-\Gamma_{\alpha\beta\gamma}$
-- statement:
--   For a smooth symmetric metric $g$, define $G_{\alpha\beta\gamma}=\partial_\alpha g_{\beta\gamma}-\partial_\beta g_{\alpha\gamma}$ and the Christoffel symbols of the first kind $\Gamma_{\alpha\beta\gamma}=\frac12(\partial_\gamma g_{\alpha\beta}+\partial_\beta g_{\alpha\gamma}-\partial_\alpha g_{\beta\gamma})$. Then
--
--   $$
--   G_{\alpha\beta\gamma} = \Gamma_{\beta\alpha\gamma}-\Gamma_{\alpha\beta\gamma}.
--   $$
--
--   So $G$ antisymmetrizes the first two indices of the Christoffel symbols (unlike torsion, which uses the last two).
-- source:
--   G. Carcassi, C. A. Aidala, "Relativity and Particle Mechanics" (note, uploaded PDF), p. 5, eq. (10), definition of G and the identity below it

import Mathlib
import Definitions.Def_RelPartMech_coordinates

open scoped ContDiff

namespace RelPartMech

theorem gSymbol_eq_christoffel_diff {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (α β γ : Fin n) (x : Coord n) :
    gSymbol g α β γ x = christoffelFirst g β α γ x - christoffelFirst g α β γ x := by sorry

end RelPartMech
