-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_retained_clause_violation_bound
-- name    : StabilityDichotomies.Bijunctive.retained_clause_violation_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:47:15.121793+00:00
-- url     : https://prove2.me/theorems/763c982b-f081-489e-9158-6efecda9d4b5
-- title:
--   A retained clause is rarely violated under exponential shifts
-- statement:
--   Fix a satisfiable feasible-root instance and a graph subinstance contained in it. Given a retained non-tautological clause and independent rate-$\beta>0$ exponential literal shifts, the probability that the score assignment violates the clause is at most $1-e^{-\beta}$. This is the fixed-subinstance estimate in the approximation analysis of Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, approximation paragraph.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.retained_clause_violation_bound {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (hF : Satisfiable F)
    (hsub : ∀ c ∈ G.constraints, c ∈ F.constraints)
    (c : Constraint Γ V) (hc : c ∈ G.constraints)
    (q : Clause (Fin c.rel.val.arity)) (hq : q ∈ rep.clauses c.rel)
    (ht : (substituteClause c q).1 ≠ literalNeg (substituteClause c q).2)
    (β : ℝ) (hβ : 0 < β) :
    ((Measure.pi (fun _ : Literal V => expMeasure β))
      {δ : Literal V → ℝ | ¬ clauseSatisfied (fun v => decide (literalScore rep G F δ (v,false) <
          literalScore rep G F δ (v,true))) (substituteClause c q)}).toReal ≤
      1 - Real.exp (-β) := by
  sorry
