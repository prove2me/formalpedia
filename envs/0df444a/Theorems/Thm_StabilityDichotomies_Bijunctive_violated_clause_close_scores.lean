-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_violated_clause_close_scores
-- name    : StabilityDichotomies.Bijunctive.violated_clause_close_scores
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:10:54.378074+00:00
-- url     : https://prove2.me/theorems/c49bc775-118b-4f24-9f5a-e137d3aafaa7
-- title:
--   A violated retained clause forces two positive scores within one
-- statement:
--   Suppose every variable has at least one positive literal score. If the score-comparison assignment violates a non-tautological clause retained in the implication graph, then the scores of the negations of the clause’s two literals are both positive and each is at most one larger than the other. This is the deterministic near-tie condition used in the source approximation proof; bounding its probability is separate.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.9, p. 20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.violated_clause_close_scores {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (δ : Literal V → ℝ)
    (hpos : ∀ v : V, ∃ b : Bool, (0 : WithBot ℝ) < literalScore rep G F δ (v,b))
    (c : Constraint Γ V) (hc : c ∈ G.constraints)
    (q : Clause (Fin c.rel.val.arity)) (hq : q ∈ rep.clauses c.rel)
    (ht : (substituteClause c q).1 ≠ literalNeg (substituteClause c q).2)
    (hviol : ¬ clauseSatisfied (fun v => decide (literalScore rep G F δ (v,false) <
      literalScore rep G F δ (v,true))) (substituteClause c q)) :
    let a := (substituteClause c q).1
    let b := (substituteClause c q).2
    (0 : WithBot ℝ) < literalScore rep G F δ (literalNeg a) ∧
    (0 : WithBot ℝ) < literalScore rep G F δ (literalNeg b) ∧
    literalScore rep G F δ (literalNeg a) ≤ literalScore rep G F δ (literalNeg b) + ((1 : ℝ) : WithBot ℝ) ∧
    literalScore rep G F δ (literalNeg b) ≤ literalScore rep G F δ (literalNeg a) + ((1 : ℝ) : WithBot ℝ) := by sorry
