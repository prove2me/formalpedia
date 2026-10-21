-- Prove2me | Theorems.Thm_QuickestOU_Detection_proposition_6
-- name    : QuickestOU.Detection.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:21.048073+00:00
-- url     : https://prove2.me/theorems/d8975cbd-2ee7-4ca1-988f-aeda491941f7
-- title:
--   Proposition 6 — value monotonicity in the observation
-- statement:
--   Fix any initial odds $\varphi\ge0$. The no-change optimal stopping value varies with the initial observation as follows:
--
--   $$x\longmapsto\widehat V(\varphi,x)\quad\text{is increasing on }(-\infty,0]\text{ and decreasing on }[0,\infty).$$
--
--   The assertion covers both sides of zero and is the value-function input to the boundary monotonicity result.
--
--   **Formalization Note** “Increasing” and “decreasing” mean weak monotonicity. The real conversion of $\widehat V$ is used on its finite value range.
-- source:
--   Glover & Peskir, Quickest detection problems for Ornstein–Uhlenbeck processes, Research Report No. 11 (2017, revised), Probab. Statist. Group Manchester; to appear in Math. Oper. Res.; https://doi.org/10.1287/moor.2021.0186; p. 17, Proposition 6 (7.13)

import Mathlib
import Definitions.Def_QuickestOU_Detection_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuickestOU.Detection

/-- Proposition 6, (7.13): the value rises toward x = 0 and falls away from it. -/
theorem proposition_6 (P : Params) (hS : P.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (hB : Driver μ B) :
    ∀ phi : ℝ, 0 ≤ phi →
      MonotoneOn (fun x => VhatR P B μ hB.meas phi x) (Set.Iic 0) ∧
      AntitoneOn (fun x => VhatR P B μ hB.meas phi x) (Set.Ici 0) := by sorry

end QuickestOU.Detection
