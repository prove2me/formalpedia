-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_violated_constraint_has_nontaut_violated_clause
-- name    : StabilityDichotomies.Bijunctive.violated_constraint_has_nontaut_violated_clause
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:56:07.512196+00:00
-- url     : https://prove2.me/theorems/d7f29118-a2eb-4cfb-8bbf-c39a52f238be
-- title:
--   A violated constraint has a violated non-tautological expanded clause
-- statement:
--   If an assignment violates an original Boolean constraint, at least one clause of its fixed defining 2-CNF expansion is violated after scope substitution, and this substituted clause is not a tautology.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, approximation paragraph.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.violated_constraint_has_nontaut_violated_clause {Γ : Language} {V : Type}
    (rep : TwoCNFRepresentation Γ) (c : Constraint Γ V) (x : V → Bool)
    (hviol : ¬ c.Satisfied x) :
    ∃ q ∈ rep.clauses c.rel,
      (substituteClause c q).1 ≠ literalNeg (substituteClause c q).2 ∧
      ¬ clauseSatisfied x (substituteClause c q) := by
  sorry
