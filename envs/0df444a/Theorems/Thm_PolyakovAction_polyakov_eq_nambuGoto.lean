-- Prove2me | Theorems.Thm_PolyakovAction_polyakov_eq_nambuGoto
-- name    : PolyakovAction.polyakov_eq_nambuGoto
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T13:04:24.77427+00:00
-- url     : https://prove2.me/theorems/1400e518-cbb7-4dc6-acbb-77646f2b98a6
-- title:
--   Polyakov action reduces to the Nambu–Goto action on-shell
-- statement:
--   Let $T$ be the string tension, $g_{\mu\nu}$ a target metric, $X$ the embedding of the worldsheet, $h_{ab}$ the worldsheet metric, and $G_{ab}=g_{\mu\nu}(X)\partial_aX^\mu\partial_bX^\nu$ the induced metric. Suppose that on a measurable worldsheet region $U$ the metric equations of motion hold,
--   $$T_{ab}=T\Big(G_{ab}-\tfrac12h_{ab}h^{cd}G_{cd}\Big)=0,$$
--   and that $h^{cd}G_{cd}\ge0$ on $U$. Then the Polyakov action equals the Nambu–Goto action:
--   $$\frac T2\int_U d^2\sigma\,\sqrt{-h}\,h^{ab}G_{ab}=T\int_U d^2\sigma\,\sqrt{-G}.$$
--
--   This is the classical equivalence of the two string actions ("Relation with Nambu–Goto action" in the source): solving the auxiliary metric's equation of motion, $\sqrt{-h}=2\sqrt{-G}/(h^{cd}G_{cd})$, and substituting back gives the Nambu–Goto action.
--
--   **Formalization Note.** The positivity $h^{cd}G_{cd}\ge0$ is implicit in the source's formula $\sqrt{-h}=2\sqrt{-G}/(h^{cd}G_{cd})$ (both square roots are non-negative); without it the two actions differ by a sign. No signature condition on $h$ is needed for the identity.
-- source:
--   Wikipedia, "Polyakov action", revision oldid=1292212311 (https://en.wikipedia.org/w/index.php?title=Polyakov_action&oldid=1292212311)

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

theorem polyakov_eq_nambuGoto {D : ℕ} (T : ℝ) (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (U : Set Worldsheet) (hU : MeasurableSet U)
    (heom : ∀ σ ∈ U, stressEnergyTensor T g h X σ = 0)
    (hpos : ∀ σ ∈ U, 0 ≤ ∑ c, ∑ d, (h σ)⁻¹ c d * inducedMetric g X σ c d) :
    polyakovAction T g h X U = nambuGotoAction T g X U := by sorry

end PolyakovAction
