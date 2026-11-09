-- Prove2me | Theorems.Thm_RecGaussColoring_Main_fact_2_3
-- name    : RecGaussColoring.Main.fact_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:54.884928+00:00
-- url     : https://prove2.me/theorems/1b451cce-a6e9-45f7-94e1-c10a38d024fb
-- title:
--   Fact 2.3 — Gaussian tail and Mills bounds
-- statement:
--   For a real threshold $t>0$, the standard Gaussian upper tail satisfies both inequalities
--   $$
--   \frac{t}{1+t^2}\frac{1}{\sqrt{2\pi}}e^{-t^2/2}
--   \ \le\ \Phi^c(t)\ \le\ e^{-t^2/2}.
--   $$
--   These bounds control Gaussian thresholds and logarithmic cardinality estimates throughout the analysis.
--
--   Differences from the source: none.
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), Fact 2.3, (2.2), p. 7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Gaussian

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- Fact 2.3, p. 7, both bounds with the printed constants. -/
theorem fact_2_3 (t : ℝ) (ht : 0 < t) :
  t/(1+t^2) * (1/Real.sqrt (2*Real.pi)) * Real.exp (-t^2/2) ≤ PhiTail t ∧
    PhiTail t ≤ Real.exp (-t^2/2) := by sorry

end RecGaussColoring.Main
