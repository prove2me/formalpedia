-- Prove2me | Theorems.Thm_RubinsteinBargaining_PEP_pep_characterization
-- name    : RubinsteinBargaining.PEP.pep_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:55:19.340394+00:00
-- url     : https://prove2.me/theorems/64ebf723-6493-4e36-90a3-d845fceaf76b
-- title:
--   THEOREM — characterization of perfect-equilibrium partitions
-- statement:
--   Assume each player's complete, reflexive, transitive preference relation satisfies (A-1)–(A-5). Let $A$ and $B$ be the perfect-equilibrium partition sets for the two opening orders, and let $\Delta_1,\Delta_2$ be the projections of the one-period threshold correspondence. Then
--
--   $$ A=\Delta_1\ne\varnothing,\qquad B=\Delta_2\ne\varnothing. $$
--
--   Both $A$ and $B$ are nonempty closed intervals. There is $e\ge0$ such that
--
--   $$ B=\{a-e:a\in A\}. $$
--
--   The result characterizes all player-1 shares obtainable from perfect equilibria, including cases with more than one partition.
--
--   **Formalization Note** A closed interval is an actual $[\ell,u]$ with $\ell\le u$; a singleton is permitted. The translate is an image under $a\mapsto a-e$, not a set difference.
-- source:
--   Rubinstein, Perfect Equilibrium in a Bargaining Model, Econometrica 50 (1982), p. 106, THEOREM, https://doi.org/10.2307/1912531

import Definitions.Def_RubinsteinBargaining_PEP_EquilibriumSets
import Definitions.Def_RubinsteinBargaining_PEP_Delta

namespace RubinsteinBargaining.PEP

theorem pep_characterization (p : Preferences) (h : FullAxioms p) :
    A p = Delta1 p ∧
    (A p).Nonempty ∧
    B p = Delta2 p ∧
    (B p).Nonempty ∧
    (∃ lo hi : ℝ, lo ≤ hi ∧ A p = Set.Icc lo hi) ∧
    (∃ lo hi : ℝ, lo ≤ hi ∧ B p = Set.Icc lo hi) ∧
    ∃ e : ℝ, 0 ≤ e ∧ B p = (fun x : ℝ => x - e) '' A p := by sorry

end RubinsteinBargaining.PEP
