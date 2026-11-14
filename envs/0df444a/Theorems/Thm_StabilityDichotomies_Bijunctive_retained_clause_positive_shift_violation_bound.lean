-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_retained_clause_positive_shift_violation_bound
-- name    : StabilityDichotomies.Bijunctive.retained_clause_positive_shift_violation_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:44:33.721212+00:00
-- url     : https://prove2.me/theorems/bf6eaff0-94cd-468a-97b8-95ef74ea7af9
-- title:
--   A retained clause is rarely violated for fixed nested subinstances
-- statement:
--   Fix a satisfiable feasible-root instance and a graph subinstance contained in it. For a retained non-tautological clause, draw independent rate-$\beta>0$ exponential shifts. The probability that all shifts are positive and the algorithm violates this clause is at most $1-e^{-\beta}$. The estimate conditions on the two subinstances, as in the approximation proof of Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, approximation paragraph.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.retained_clause_positive_shift_violation_bound {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (hF : Satisfiable F)
    (hsub : ∀ c ∈ G.constraints, c ∈ F.constraints)
    (c : Constraint Γ V) (hc : c ∈ G.constraints)
    (q : Clause (Fin c.rel.val.arity)) (hq : q ∈ rep.clauses c.rel)
    (ht : (substituteClause c q).1 ≠ literalNeg (substituteClause c q).2)
    (β : ℝ) (hβ : 0 < β) :
    ((Measure.pi (fun _ : Literal V => expMeasure β))
      {δ : Literal V → ℝ | (∀ a, 0 < δ a) ∧
        ¬ clauseSatisfied (fun v => decide (literalScore rep G F δ (v,false) <
          literalScore rep G F δ (v,true))) (substituteClause c q)}).toReal ≤
      1 - Real.exp (-β) := by
  sorry
