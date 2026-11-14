-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_exponential_memoryless_tail
-- name    : StabilityDichotomies.Bijunctive.exponential_memoryless_tail
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:32:52.397177+00:00
-- url     : https://prove2.me/theorems/8d068df3-250d-49a4-a604-d52625222c39
-- title:
--   Memoryless tail identity for exponential shifts
-- statement:
--   For a rate-$\beta>0$ exponential variable $X$ and $d,t\ge0$, $\Pr[X>d+t]=\Pr[X>d]\Pr[X>t]$. This is the survival-function form of memorylessness used for positive shifted root scores.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

theorem StabilityDichotomies.Bijunctive.exponential_memoryless_tail (β d t : ℝ) (hβ : 0 < β) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    (expMeasure β).real (Ioi (d+t)) =
      (expMeasure β).real (Ioi d) * (expMeasure β).real (Ioi t) := by
  sorry
