-- Prove2me | Theorems.Thm_RubinsteinBargaining_PEP_proposition_1
-- name    : RubinsteinBargaining.PEP.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:53:21.738672+00:00
-- url     : https://prove2.me/theorems/464d631c-f470-474b-b434-cf7ae3a12d52
-- title:
--   Proposition 1 — Δ pairs induce equilibria
-- statement:
--   Every pair $(x,y)\in\Delta$ provides a perfect-equilibrium partition in each opening order:
--
--   $$ (x,y)\in\Delta\quad\Longrightarrow\quad x\in A\ \text{and}\ y\in B. $$
--
--   This establishes one direction of the final characterization under the paper's full preference axioms.
-- source:
--   Rubinstein, Perfect Equilibrium in a Bargaining Model, Econometrica 50 (1982), p. 104, Proposition 1, https://doi.org/10.2307/1912531

import Definitions.Def_RubinsteinBargaining_PEP_EquilibriumSets
import Definitions.Def_RubinsteinBargaining_PEP_Delta

namespace RubinsteinBargaining.PEP

theorem proposition_1 (p : Preferences) (h : FullAxioms p) :
    ∀ x y : Partition, (x.val, y.val) ∈ Delta p →
      x.val ∈ A p ∧ y.val ∈ B p := by sorry

end RubinsteinBargaining.PEP
