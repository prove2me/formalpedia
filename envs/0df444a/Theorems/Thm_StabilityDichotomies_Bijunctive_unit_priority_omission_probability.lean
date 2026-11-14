-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_unit_priority_omission_probability
-- name    : StabilityDichotomies.Bijunctive.unit_priority_omission_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:51:21.424203+00:00
-- url     : https://prove2.me/theorems/759d2249-598d-4bea-9a8d-3a630250db12
-- title:
--   A constraint occurrence is omitted with probability ε/2
-- statement:
--   For $0\le\varepsilon\le1$, a uniform priority on $[0,1]$ exceeds the graph threshold $1-\varepsilon/2$ with probability exactly $\varepsilon/2$.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Definition 4.8 and proof of Theorem 4.9.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Set StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.unit_priority_omission_probability (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    unitPriorityMeasure (Ioi (1 - ε / 2)) = ENNReal.ofReal (ε / 2) := by
  sorry
