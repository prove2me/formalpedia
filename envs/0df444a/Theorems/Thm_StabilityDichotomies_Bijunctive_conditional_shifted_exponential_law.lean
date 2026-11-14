-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_shifted_exponential_law
-- name    : StabilityDichotomies.Bijunctive.conditional_shifted_exponential_law
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:35:10.172673+00:00
-- url     : https://prove2.me/theorems/ec641362-1d41-44b9-8ae9-ab028d636357
-- title:
--   A conditioned positive exponential excess has the original law
-- statement:
--   Let $X$ be rate-$\beta>0$ exponential and let $d\ge0$. Condition on $X>d$ and subtract $d$. The resulting probability law is again rate-$\beta$ exponential. This is the one-coordinate conditional law needed in the feasibility-root record analysis.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

theorem StabilityDichotomies.Bijunctive.conditional_shifted_exponential_law (β d : ℝ) (hβ : 0 < β) (hd : 0 ≤ d) :
    (ProbabilityTheory.cond (expMeasure β) (Ioi d)).map (fun x : ℝ => x - d) = expMeasure β := by
  sorry
