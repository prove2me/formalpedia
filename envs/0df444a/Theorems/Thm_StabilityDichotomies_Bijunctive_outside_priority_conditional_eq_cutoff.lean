-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_outside_priority_conditional_eq_cutoff
-- name    : StabilityDichotomies.Bijunctive.outside_priority_conditional_eq_cutoff
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:22:52.12821+00:00
-- url     : https://prove2.me/theorems/ce5f255c-df77-461a-b118-6ec365ce61cd
-- title:
--   An excluded first-stage priority has the cutoff distribution
-- statement:
--   Let a priority be uniformly distributed on $[0,1]$, and suppose $0<\varepsilon\le1$. Conditional on the priority exceeding $1-\varepsilon/2$, its distribution is uniform on $[1-\varepsilon/2,1]$, the same as the algorithm’s cutoff.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, conditioning on the first-stage constraint set.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.outside_priority_conditional_eq_cutoff (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ProbabilityTheory.cond unitPriorityMeasure (Ioi (1 - ε / 2)) = cutoffMeasure ε := by
  sorry
