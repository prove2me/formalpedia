-- Prove2me | Theorems.Thm_RelPartMech_covDeriv_antisymm
-- name    : RelPartMech.covDeriv_antisymm
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:12:05.896696+00:00
-- url     : https://prove2.me/theorems/44ecd607-a78e-4c28-84a7-eea9f1d45dea
-- title:
--   Antisymmetrized covariant derivative equals antisymmetrized partial derivative
-- statement:
--   For the Levi-Civita connection of a smooth metric $g$ and any covector field $A_\beta$, with $\nabla_\alpha A_\beta=\partial_\alpha A_\beta-\Gamma^\gamma_{\beta\alpha}A_\gamma$,
--
--   $$
--   \nabla_\alpha A_\beta-\nabla_\beta A_\alpha = \partial_\alpha A_\beta-\partial_\beta A_\alpha .
--   $$
-- source:
--   G. Carcassi, C. A. Aidala, "Relativity and Particle Mechanics" (note, uploaded PDF), p. 8, eq. (15), first two lines

import Mathlib
import Definitions.Def_RelPartMech_coordinates

open scoped ContDiff

namespace RelPartMech

theorem covDeriv_antisymm {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (α β : Fin n) (x : Coord n) :
    covDerivCov g A α β x - covDerivCov g A β α x = pd α (A β) x - pd β (A α) x := by sorry

end RelPartMech
