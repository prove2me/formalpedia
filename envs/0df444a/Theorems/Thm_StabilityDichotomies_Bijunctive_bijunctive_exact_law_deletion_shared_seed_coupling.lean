-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_exact_law_deletion_shared_seed_coupling
-- name    : StabilityDichotomies.Bijunctive.bijunctive_exact_law_deletion_shared_seed_coupling
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:45:35.896056+00:00
-- url     : https://prove2.me/theorems/88fa8fb9-daf9-47c9-8e85-a7c9f7df80e2
-- title:
--   Exact bijunctive output laws admit the source common-seed deletion coupling
-- statement:
--   For a satisfiable instance and a constraint occurrence, couple the exact Definition 4.8 output laws before and after deletion by sharing all remaining occurrence priorities, the cutoff, and the literal shifts. Their Wasserstein distance is at most the sum over variables of the probabilities that the coupled outputs disagree. The equivalence specifies the deleted occurrence and reindexes all other priorities.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, common-randomness deletion coupling.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.bijunctive_exact_law_deletion_shared_seed_coupling {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (c : Constraint Γ V)
    (hc : c ∈ I.constraints) (hI : Satisfiable I) (ε : ℝ) (hε : 0 < ε)
    (A : Solver Γ) (hLaw : BijunctiveOutputLaw Γ rep ε A)
    (e : Fin I.constraints.card ≃ Option (Fin (I.delete c).constraints.card)) :
    wasserstein (A V I) (A V (I.delete c)) ≤
      ∑ v : V, (bijunctiveSeedMeasure rep I ε
        {z | bijunctiveOutput rep I ε z.1 z.2.1 z.2.2 v ≠
          bijunctiveOutput rep (I.delete c) ε (fun i => z.1 (e.symm (some i))) z.2.1 z.2.2 v}).toReal := by
  sorry
