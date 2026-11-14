-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_retained_occurrence_clause_violation_seed_bound
-- name    : StabilityDichotomies.Bijunctive.retained_occurrence_clause_violation_seed_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:54:09.168649+00:00
-- url     : https://prove2.me/theorems/e8e5410b-0c22-4b66-a126-451e55ad790c
-- title:
--   A retained occurrence rarely violates an expanded clause under the full seed law
-- statement:
--   For a satisfiable input and $\varepsilon>0$, fix an occurrence and a non-tautological clause in its 2-CNF expansion. Under the complete Definition 4.8 product seed law, the probability that the occurrence is retained in the graph subinstance and the output violates this clause is at most $1-e^{-\beta}$, where $\beta=\varepsilon/(2b_\Gamma)$.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, approximation paragraph.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.retained_occurrence_clause_violation_seed_bound {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (ε : ℝ) (hε : 0 < ε) (i : Fin I.constraints.card)
    (q : Clause (Fin (occurrenceAt I i).rel.val.arity)) (hq : q ∈ rep.clauses (occurrenceAt I i).rel)
    (ht : (substituteClause (occurrenceAt I i) q).1 ≠ literalNeg (substituteClause (occurrenceAt I i) q).2) :
    (bijunctiveSeedMeasure rep I ε
      {seed | seed.1 i ≤ 1 - ε / 2 ∧
        ¬ clauseSatisfied (bijunctiveOutput rep I ε seed.1 seed.2.1 seed.2.2)
          (substituteClause (occurrenceAt I i) q)}).toReal ≤
      1 - Real.exp (-bijunctiveRate rep ε) := by
  sorry
