-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_occurrence_violation_seed_bound
-- name    : StabilityDichotomies.Bijunctive.bijunctive_occurrence_violation_seed_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:59:12.959378+00:00
-- url     : https://prove2.me/theorems/3e3f4cb9-55c5-408e-802a-e7c545069e33
-- title:
--   Each occurrence is violated with probability at most ε
-- statement:
--   For a satisfiable instance, $0<\varepsilon\le1$, and any original constraint occurrence, the probability under the exact Definition 4.8 seed law that the output violates that occurrence is at most $\varepsilon$. The result counts repeated occurrences separately.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, approximation paragraph.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.bijunctive_occurrence_violation_seed_bound {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (i : Fin I.constraints.card) :
    (bijunctiveSeedMeasure rep I ε
      {seed | ¬ (occurrenceAt I i).Satisfied (bijunctiveOutput rep I ε seed.1 seed.2.1 seed.2.2)}).toReal ≤ ε := by
  sorry
