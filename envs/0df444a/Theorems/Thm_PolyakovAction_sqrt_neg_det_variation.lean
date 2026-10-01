-- Prove2me | Theorems.Thm_PolyakovAction_sqrt_neg_det_variation
-- name    : PolyakovAction.sqrt_neg_det_variation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T10:53:06.834729+00:00
-- url     : https://prove2.me/theorems/2ac48007-231a-486f-8dfb-541d3310ac52
-- title:
--   Variation of $\sqrt{-h}$ with respect to $h^{ab}$
-- statement:
--   Let $h^{ab}$ be a symmetric $2\times2$ matrix with negative determinant and $h_{ab}$ its inverse, so $h=\det h_{ab}<0$. For every variation $\delta h^{ab}$,
--   $$\delta\sqrt{-h}=-\frac12\sqrt{-h}\,h_{ab}\,\delta h^{ab},$$
--   in the sense that $t\mapsto\sqrt{-\det\big((h^{ab}+t\,\delta h^{ab})^{-1}\big)}$ has derivative $-\frac12\sqrt{-h}\,h_{ab}\delta h^{ab}$ at $t=0$.
--
--   This is the identity used in the source ("Knowing also that") to compute the variational derivative of the action with respect to the inverse metric.
--
--   **Formalization Note.** The variation is formalized as a directional derivative in the space of inverse metrics.
-- source:
--   Wikipedia, "Polyakov action", revision oldid=1292212311 (https://en.wikipedia.org/w/index.php?title=Polyakov_action&oldid=1292212311)

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

theorem sqrt_neg_det_variation (k δk : Matrix (Fin 2) (Fin 2) ℝ) (hk : k.det < 0)
    (hksymm : kᵀ = k) :
    HasDerivAt (fun t : ℝ => Real.sqrt (-((k + t • δk)⁻¹).det))
      (-(1 / 2) * Real.sqrt (-(k⁻¹).det) * ∑ a, ∑ b, k⁻¹ a b * δk a b) 0 := by sorry

end PolyakovAction
