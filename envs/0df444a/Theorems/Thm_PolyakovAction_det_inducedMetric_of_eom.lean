-- Prove2me | Theorems.Thm_PolyakovAction_det_inducedMetric_of_eom
-- name    : PolyakovAction.det_inducedMetric_of_eom
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-01T11:14:06.70614+00:00
-- url     : https://prove2.me/theorems/4a007aa3-36d9-4ade-b63e-70b29e5db4bb
-- title:
--   On-shell determinant of the induced metric
-- statement:
--   Let $T\neq0$. If the metric equation of motion $T_{ab}=T\big(G_{ab}-\tfrac12h_{ab}h^{cd}G_{cd}\big)=0$ holds at a worldsheet point, then there
--   $$G=\det(G_{ab})=\frac14\,h\,\big(h^{cd}G_{cd}\big)^2,\qquad h=\det(h_{ab}).$$
--
--   This is the step of the source's "Relation with Nambu–Goto action" that leads to $\sqrt{-h}=2\sqrt{-G}/(h^{cd}G_{cd})$.
-- source:
--   Wikipedia, "Polyakov action", revision oldid=1292212311 (https://en.wikipedia.org/w/index.php?title=Polyakov_action&oldid=1292212311)

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

theorem det_inducedMetric_of_eom {D : ℕ} (T : ℝ) (hT : T ≠ 0)
    (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (σ : Worldsheet) (heom : stressEnergyTensor T g h X σ = 0) :
    (inducedMetric g X σ).det
      = 1 / 4 * (h σ).det * (∑ c, ∑ d, (h σ)⁻¹ c d * inducedMetric g X σ c d) ^ 2 := by sorry

end PolyakovAction
