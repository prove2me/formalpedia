-- Prove2me | Theorems.Thm_QuickestOU_Detection_corollary_7
-- name    : QuickestOU.Detection.corollary_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:26.248824+00:00
-- url     : https://prove2.me/theorems/dc1667a2-18be-41be-b495-17b724f80005
-- title:
--   Corollary 7 — boundary monotonicity
-- statement:
--   For the boundary $b(x)=\inf\{\varphi\ge0:\widehat V(\varphi,x)=0\}$ of the optimal stopping region,
--
--   $$b\text{ is decreasing on }(-\infty,0]\quad\text{and increasing on }[0,\infty).$$
--
--   This records how the odds threshold changes as the initial observation moves away from zero.
--
--   **Formalization Note** Monotonicity is weak; the theorem refers to the boundary derived from the stopping value, rather than to an arbitrary solution of the integral equation.
-- source:
--   Glover & Peskir, Quickest detection problems for Ornstein–Uhlenbeck processes, Research Report No. 11 (2017, revised), Probab. Statist. Group Manchester; to appear in Math. Oper. Res.; https://doi.org/10.1287/moor.2021.0186; p. 20, Corollary 7

import Mathlib
import Definitions.Def_QuickestOU_Detection_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuickestOU.Detection

/-- Corollary 7: the boundary falls toward x = 0 and rises away from it. -/
theorem corollary_7 (P : Params) (hS : P.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (hB : Driver μ B) :
    AntitoneOn (bnd P B μ hB.meas) (Set.Iic 0) ∧
      MonotoneOn (bnd P B μ hB.meas) (Set.Ici 0) := by sorry

end QuickestOU.Detection
