-- Prove2me | Theorems.Thm_RelPartMech_covDeriv_antisymm_contra
-- name    : RelPartMech.covDeriv_antisymm_contra
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:12:25.837479+00:00
-- url     : https://prove2.me/theorems/3833e9d2-15db-4c1c-b750-b11b1df41fd8
-- title:
--   Antisymmetrized raised covariant derivative and $G$
-- statement:
--   For the Levi-Civita connection of a smooth metric $g$, a covector field $A_\gamma$ and $A^\beta=g^{\beta\gamma}A_\gamma$, with $\nabla_\alpha A^\beta=\partial_\alpha A^\beta+\Gamma^\beta_{\gamma\alpha}A^\gamma$ and $\nabla^\alpha=g^{\alpha\gamma}\nabla_\gamma$,
--
--   $$
--   \nabla^\alpha A^\beta-\nabla^\beta A^\alpha = \partial^\alpha A^\beta-\partial^\beta A^\alpha + G^{\alpha\beta\gamma}A_\gamma .
--   $$
--
--   With contravariant indices the antisymmetrized covariant and partial derivatives differ, and $G$ expresses the difference.
-- source:
--   G. Carcassi, C. A. Aidala, "Relativity and Particle Mechanics" (note, uploaded PDF), p. 8, eq. (15), last block

import Mathlib
import Definitions.Def_RelPartMech_coordinates

open scoped ContDiff

namespace RelPartMech

theorem covDeriv_antisymm_contra {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (α β : Fin n) (x : Coord n) :
    ∑ γ, ginv g x α γ * covDerivContra g (raise g A) γ β x
      - ∑ γ, ginv g x β γ * covDerivContra g (raise g A) γ α x =
      pdUp g α (raise g A β) x - pdUp g β (raise g A α) x
        + ∑ γ, gSymbolUp g α β γ x * A γ x := by sorry

end RelPartMech
