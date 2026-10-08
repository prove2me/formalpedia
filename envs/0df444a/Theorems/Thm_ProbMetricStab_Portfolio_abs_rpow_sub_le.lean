-- Prove2me | Theorems.Thm_ProbMetricStab_Portfolio_abs_rpow_sub_le
-- name    : ProbMetricStab.Portfolio.abs_rpow_sub_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:55.59105+00:00
-- url     : https://prove2.me/theorems/d2480889-f550-4098-835a-50e60510c5ed
-- title:
--   Proof of Theorem 5.2, p. 25 — sup_{t∈[−1,1]} ||t|^α − |t|^α̃| ≤ e⁻¹|α − α̃|
-- statement:
--   For all $\alpha,\tilde\alpha\in(1,2)$ and every $t\in[-1,1]$,
--   $$\big||t|^\alpha-|t|^{\tilde\alpha}\big|\le e^{-1}|\alpha-\tilde\alpha|,$$
--   where $e=\exp(1)$. Equivalently, $\sup_{t\in[-1,1]}\big||t|^\alpha-|t|^{\tilde\alpha}\big|\le e^{-1}|\alpha-\tilde\alpha|$.
--
--   This is the step of the proof of Theorem 5.2 that turns a change of the stability index into a change of the risk.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 25, proof of Theorem 5.2, last inequality of the first display

import Mathlib
import Definitions.Def_ProbMetricStab_Portfolio_Setting

open MeasureTheory
open scoped ENNReal

namespace ProbMetricStab.Portfolio
theorem abs_rpow_sub_le (α α' : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (hα'1 : 1 < α') (hα'2 : α' < 2)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |(|t| ^ α - |t| ^ α')| ≤ Real.exp (-1) * |α - α'| := by sorry
end ProbMetricStab.Portfolio
