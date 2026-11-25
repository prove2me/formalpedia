-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_partial_assignment_of_clause_matching
-- name    : RandomCNFDeficiency.LowerBound.partial_assignment_of_clause_matching
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-25T19:57:29.573894+00:00
-- url     : https://prove2.me/theorems/bd073900-6d0e-44c7-8527-fb537ad0d6ed
-- title:
--   A distinct-variable clause matching yields a consistent partial assignment
-- statement:
--   Let $H$ be a finite family of signed clauses and $S$ a protected variable set. Suppose $m:H\to[n]$ is injective and $m(C)\in\operatorname{Vars}(C)\setminus S$ for every clause. There exists a partial Boolean assignment $\rho:[n]\to\{0,1,\bot\}$ such that
--
--   $$\rho\models C\ \text{for every }C\in H,\qquad \rho(i)=\bot\ \text{for every }i\in S.$$
--
--   Here $\bot$ means unassigned, and partial satisfaction requires an actually assigned literal with its satisfying value. This converts a clause matching into a consistent local assignment.
-- source:
--   Jonas Conneryd, Random (log n)-CNF Formulas Are Hard for Depth-2 Frege with Modular Gates, manuscript dated November 2, 2026, STOC 2027 submission #332, Lemma 3.5, final assignment construction, printed pp. 10–11 / PDF pp. 12–13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
open RandomCNFDeficiency.LowerBound

theorem RandomCNFDeficiency.LowerBound.partial_assignment_of_clause_matching {n : ℕ} (H : CNF n) (S : Finset (Fin n))
    (m : {C // C ∈ H} → Fin n) (hm : Function.Injective m)
    (hs : ∀ C, m C ∈ clauseSupport C.1 ∧ m C ∉ S) :
    ∃ ρ : Fin n → Option Bool,
      (∀ C ∈ H, PartialSatisfies ρ C) ∧ ∀ i ∈ S, ρ i=none := by sorry
