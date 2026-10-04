-- Prove2me | Theorems.Thm_PolyakovAction_conformal_gauge_constraints
-- name    : PolyakovAction.conformal_gauge_constraints
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-01T12:24:26.422015+00:00
-- url     : https://prove2.me/theorems/30ddb66b-c6cc-478c-8428-a6c6cd6c866e
-- title:
--   Constraints in conformal gauge
-- statement:
--   Let $T\neq0$ and work in conformal gauge $h_{ab}=\eta_{ab}=\mathrm{diag}(1,-1)$. At a worldsheet point, the stress–energy tensor vanishes, $T_{ab}=0$, if and only if
--   $$T_{01}=T_{10}=\dot X\cdot X'=0,\qquad T_{00}=T_{11}=\tfrac12\big(\dot X^2+X'^2\big)=0,$$
--   i.e. $G_{01}=G_{10}=0$ and $G_{00}+G_{11}=0$.
--
--   These are the constraints of the source's "Equations of motion" section.
--
--   **Formalization Note.** Both off-diagonal components $G_{01}$ and $G_{10}$ appear because no symmetry of the target metric is assumed.
-- source:
--   Wikipedia, "Polyakov action", revision oldid=1292212311 (https://en.wikipedia.org/w/index.php?title=Polyakov_action&oldid=1292212311)

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

theorem conformal_gauge_constraints {D : ℕ} (T : ℝ) (hT : T ≠ 0)
    (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ) (X : Worldsheet → Spacetime D)
    (σ : Worldsheet) :
    stressEnergyTensor T g (fun _ => minkowskiMetric 2) X σ = 0 ↔
      (inducedMetric g X σ 0 1 = 0 ∧ inducedMetric g X σ 1 0 = 0 ∧
        inducedMetric g X σ 0 0 + inducedMetric g X σ 1 1 = 0) := by sorry

end PolyakovAction
