-- Prove2me | Theorems.Thm_RubinsteinBargaining_PEP_proposition_4
-- name    : RubinsteinBargaining.PEP.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:55:22.906379+00:00
-- url     : https://prove2.me/theorems/abdfc60f-6b94-4d6b-a740-a794c3be5b90
-- title:
--   Proposition 4 — all equilibria lie in Δ's projections
-- statement:
--   Every perfect-equilibrium partition is in the corresponding projection of $\Delta$:
--
--   $$ A\subseteq\Delta_1,\qquad B\subseteq\Delta_2. $$
--
--   Together with Proposition 1, this supplies the equality part of the main theorem.
-- source:
--   Rubinstein, Perfect Equilibrium in a Bargaining Model, Econometrica 50 (1982), p. 106, Proposition 4, https://doi.org/10.2307/1912531

import Definitions.Def_RubinsteinBargaining_PEP_EquilibriumSets
import Definitions.Def_RubinsteinBargaining_PEP_Delta

namespace RubinsteinBargaining.PEP

theorem proposition_4 (p : Preferences) (h : FullAxioms p) :
    A p ⊆ Delta1 p ∧ B p ⊆ Delta2 p := by sorry

end RubinsteinBargaining.PEP
