-- Prove2me | Theorems.Thm_RubinsteinBargaining_PEP_proposition_2
-- name    : RubinsteinBargaining.PEP.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:53:23.840198+00:00
-- url     : https://prove2.me/theorems/ab2e72e2-d0c4-4186-87c9-9383b63ba9ee
-- title:
--   Proposition 2 — Δ and the equilibrium sets are nonempty
-- statement:
--   The threshold correspondence contains a pair, so both opening orders admit a perfect-equilibrium partition:
--
--   $$ \Delta\ne\varnothing,\qquad A\ne\varnothing,\qquad B\ne\varnothing. $$
--
--   This is the existence component of the paper's main theorem.
-- source:
--   Rubinstein, Perfect Equilibrium in a Bargaining Model, Econometrica 50 (1982), p. 105, Proposition 2, https://doi.org/10.2307/1912531

import Definitions.Def_RubinsteinBargaining_PEP_EquilibriumSets
import Definitions.Def_RubinsteinBargaining_PEP_Delta

namespace RubinsteinBargaining.PEP

theorem proposition_2 (p : Preferences) (h : FullAxioms p) :
    (Delta p).Nonempty ∧ (A p).Nonempty ∧ (B p).Nonempty := by sorry

end RubinsteinBargaining.PEP
