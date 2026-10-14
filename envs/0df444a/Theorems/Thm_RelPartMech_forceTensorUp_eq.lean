-- Prove2me | Theorems.Thm_RelPartMech_forceTensorUp_eq
-- name    : RelPartMech.forceTensorUp_eq
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:09:25.818986+00:00
-- url     : https://prove2.me/theorems/299cbef8-eae7-4d09-aced-6b497cf85429
-- title:
--   Raised force tensor: $F^{\alpha\beta}=\partial^\alpha A^\beta-\partial^\beta A^\alpha+G^{\alpha\beta\gamma}A_\gamma$
-- statement:
--   For a smooth metric $g$ and smooth covector field $A_\alpha$ with $A^\alpha=g^{\alpha\beta}A_\beta$, let $F_{\alpha\beta}=\partial_\alpha A_\beta-\partial_\beta A_\alpha$ and $F^{\alpha\beta}=g^{\alpha\gamma}g^{\beta\delta}F_{\gamma\delta}$. Then
--
--   $$
--   F^{\alpha\beta} = \partial^\alpha A^\beta-\partial^\beta A^\alpha+G^{\alpha\beta\gamma}A_\gamma .
--   $$
--
--   Unlike the covariant version, the raised force tensor is not the antisymmetrized raised derivative; $G$ measures the difference.
-- source:
--   G. Carcassi, C. A. Aidala, "Relativity and Particle Mechanics" (note, uploaded PDF), p. 5, eq. (11), second block

import Mathlib
import Definitions.Def_RelPartMech_coordinates

open scoped ContDiff

namespace RelPartMech

theorem forceTensorUp_eq {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α)) (α β : Fin n) (x : Coord n) :
    forceTensorUp g A α β x =
      pdUp g α (raise g A β) x - pdUp g β (raise g A α) x
        + ∑ γ, gSymbolUp g α β γ x * A γ x := by sorry

end RelPartMech
