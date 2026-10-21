-- Prove2me | Theorems.Thm_QuickestOU_Detection_proposition_9
-- name    : QuickestOU.Detection.proposition_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:22.885998+00:00
-- url     : https://prove2.me/theorems/bbe49d0c-e549-4a32-85f8-42e25ff71519
-- title:
--   Proposition 9 — continuity of the stopping boundary
-- statement:
--   The optimal stopping threshold $b$, defined from the zero set of the no-change value, is continuous on the entire real line:
--
--   $$b:\mathbb R\longrightarrow\mathbb R\quad\text{is continuous}.$$
--
--   This regularity enters the class in which the nonlinear integral equation has a unique boundary solution.
-- source:
--   Glover & Peskir, Quickest detection problems for Ornstein–Uhlenbeck processes, Research Report No. 11 (2017, revised), Probab. Statist. Group Manchester; to appear in Math. Oper. Res.; https://doi.org/10.1287/moor.2021.0186; p. 21, Proposition 9

import Mathlib
import Definitions.Def_QuickestOU_Detection_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuickestOU.Detection

/-- Proposition 9: continuity of the optimal stopping boundary. -/
theorem proposition_9 (P : Params) (hS : P.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (hB : Driver μ B) :
    Continuous (bnd P B μ hB.meas) := by sorry

end QuickestOU.Detection
