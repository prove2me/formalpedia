-- Prove2me | Theorems.Thm_QuickestOU_Detection_measure_change
-- name    : QuickestOU.Detection.measure_change
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:28.812988+00:00
-- url     : https://prove2.me/theorems/7bf99572-8bbb-4269-b0d2-4c39c9059a57
-- title:
--   (4.6)–(4.7) — measure-change identity for the Bayes risk
-- statement:
--   For a prior $\pi\in[0,1)$ and initial observation $x$, let $V(\pi)$ be the infimum of the original false-alarm and delay risk, and let $\widehat V(\varphi,x)$ be the no-change optimal stopping value. Then
--
--   $$V(\pi)=(1-\pi)\left[1+c\,\widehat V\left(\frac{\pi}{1-\pi},x\right)\right].$$
--
--   The identity transfers the Bayesian problem to the two-dimensional no-change problem, while keeping the two infima defined from their own stopping-time classes.
--
--   **Formalization Note** The no-change and disorder models may be carried on different probability spaces. The prior is below one because the posterior-odds initial value uses $\pi/(1-\pi)$.
-- source:
--   Glover & Peskir, Quickest detection problems for Ornstein–Uhlenbeck processes, Research Report No. 11 (2017, revised), Probab. Statist. Group Manchester; to appear in Math. Oper. Res.; https://doi.org/10.1287/moor.2021.0186; p. 9, (4.6)–(4.7)

import Mathlib
import Definitions.Def_QuickestOU_Detection_Disorder

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuickestOU.Detection

/-- Equations (4.6)--(4.8): change from the disorder law to the no-change law. -/
theorem measure_change (P : Params) (hS : P.Standing) (x p0 : ℝ)
    (hp0 : 0 ≤ p0) (hp1 : p0 < 1) (M : DisorderModel P p0 x)
    {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω')
    (B' : ℝ≥0 → Ω' → ℝ) (hB' : Driver μ' B') :
    (Vpi M).toReal = (1 - p0) *
      (1 + P.c * VhatR P B' μ' hB'.meas (p0 / (1 - p0)) x) := by sorry

end QuickestOU.Detection
