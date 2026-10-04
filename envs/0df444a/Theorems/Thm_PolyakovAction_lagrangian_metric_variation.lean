-- Prove2me | Theorems.Thm_PolyakovAction_lagrangian_metric_variation
-- name    : PolyakovAction.lagrangian_metric_variation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-01T10:58:59.715932+00:00
-- url     : https://prove2.me/theorems/628414ba-abe6-41d8-a16c-1b2564adc029
-- title:
--   Variational derivative of the action with respect to $h^{ab}$
-- statement:
--   Let $h^{ab}$ be a symmetric $2\times2$ matrix with negative determinant, $h_{ab}$ its inverse, and $G_{ab}$ any $2\times2$ matrix. For every variation $\delta h^{ab}$ the Polyakov density $\sqrt{-h}\,h^{ab}G_{ab}$ varies as
--   $$\delta\big(\sqrt{-h}\,h^{ab}G_{ab}\big)=\sqrt{-h}\Big(G_{ab}-\frac12h_{ab}h^{cd}G_{cd}\Big)\delta h^{ab}.$$
--   With $G_{ab}=g_{\mu\nu}\partial_aX^\mu\partial_bX^\nu$ this is the source's formula
--   $$\frac{\delta S}{\delta h^{ab}}=\frac T2\sqrt{-h}\Big(G_{ab}-\frac12h_{ab}h^{cd}G_{cd}\Big).$$
--
--   **Formalization Note.** Formalized pointwise, as the derivative at $t=0$ of the density along the line $h^{ab}+t\,\delta h^{ab}$ in the space of inverse metrics; the overall factor $T/2$ is omitted.
-- source:
--   Wikipedia, "Polyakov action", revision oldid=1292212311 (https://en.wikipedia.org/w/index.php?title=Polyakov_action&oldid=1292212311)

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

theorem lagrangian_metric_variation (k δk G : Matrix (Fin 2) (Fin 2) ℝ) (hk : k.det < 0)
    (hksymm : kᵀ = k) :
    HasDerivAt
      (fun t : ℝ => Real.sqrt (-((k + t • δk)⁻¹).det) * ∑ a, ∑ b, (k + t • δk) a b * G a b)
      (Real.sqrt (-(k⁻¹).det) *
        ∑ a, ∑ b, (G a b - 1 / 2 * k⁻¹ a b * ∑ c, ∑ d, k c d * G c d) * δk a b) 0 := by sorry

end PolyakovAction
