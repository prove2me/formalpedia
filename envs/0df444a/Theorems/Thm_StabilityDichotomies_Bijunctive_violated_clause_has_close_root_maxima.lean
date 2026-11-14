-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_violated_clause_has_close_root_maxima
-- name    : StabilityDichotomies.Bijunctive.violated_clause_has_close_root_maxima
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:40:21.624205+00:00
-- url     : https://prove2.me/theorems/dc534e6f-948d-4d73-aecb-46b9b9fc24be
-- title:
--   A violated retained clause has close feasible-root maxima
-- statement:
--   Assume the graph subinstance is contained in the feasible-root subinstance and each variable has a positive literal score. If a retained non-tautological clause is violated, there are distinct feasible roots reaching the negations of its two literals. Each root attains the maximum score contribution among feasible roots reaching that literal, and the two maxima differ by at most one.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, approximation paragraph.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.violated_clause_has_close_root_maxima {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (δ : Literal V → ℝ)
    (hsub : ∀ c ∈ G.constraints, c ∈ F.constraints)
    (hpos : ∀ v : V, ∃ b : Bool, (0 : WithBot ℝ) < literalScore rep G F δ (v,b))
    (c : Constraint Γ V) (hc : c ∈ G.constraints)
    (q : Clause (Fin c.rel.val.arity)) (hq : q ∈ rep.clauses c.rel)
    (ht : (substituteClause c q).1 ≠ literalNeg (substituteClause c q).2)
    (hviol : ¬ clauseSatisfied (fun v => decide (literalScore rep G F δ (v,false) <
      literalScore rep G F δ (v,true))) (substituteClause c q)) :
    let a := literalNeg (substituteClause c q).1
    let b := literalNeg (substituteClause c q).2
    ∃ u v : Literal V, ∃ n m : ℕ, u ≠ v ∧ feasibleLiteral F u ∧ feasibleLiteral F v ∧
      implicationDistance rep G u a = some n ∧ implicationDistance rep G v b = some m ∧
      (∀ r k, feasibleLiteral F r → implicationDistance rep G r a = some k → δ r - k ≤ δ u - n) ∧
      (∀ r k, feasibleLiteral F r → implicationDistance rep G r b = some k → δ r - k ≤ δ v - m) ∧
      (δ u - n) - (δ v - m) ≤ 1 ∧ (δ v - m) - (δ u - n) ≤ 1 := by
  sorry
