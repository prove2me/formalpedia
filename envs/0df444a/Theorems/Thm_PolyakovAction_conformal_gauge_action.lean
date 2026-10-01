-- Prove2me | Theorems.Thm_PolyakovAction_conformal_gauge_action
-- name    : PolyakovAction.conformal_gauge_action
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T11:39:22.493473+00:00
-- url     : https://prove2.me/theorems/61052a09-0b1e-49fc-950b-6a99325d445a
-- title:
--   The Polyakov action in conformal gauge
-- statement:
--   In conformal gauge, $h_{ab}=\eta_{ab}=\mathrm{diag}(1,-1)$, the Polyakov action becomes
--   $$S=\frac T2\int d^2\sigma\,\sqrt{-\eta}\,\eta^{ab}g_{\mu\nu}(X)\partial_aX^\mu\partial_bX^\nu=\frac T2\int d^2\sigma\,\big(\dot X^2-X'^2\big),$$
--   where $\dot X^2=g_{\mu\nu}\dot X^\mu\dot X^\nu$, $X'^2=g_{\mu\nu}X'^\mu X'^\nu$, $\dot X=\partial_\tau X$, $X'=\partial_\sigma X$.
--
--   **Formalization Note.** The identity holds for any target metric $g$ and region $U$; the gauge-fixing step itself (using diffeomorphisms and Weyl rescalings to reach $\eta$) is not part of this statement.
-- source:
--   Wikipedia, "Polyakov action", revision oldid=1292212311 (https://en.wikipedia.org/w/index.php?title=Polyakov_action&oldid=1292212311)

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

theorem conformal_gauge_action {D : ℕ} (T : ℝ) (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (X : Worldsheet → Spacetime D) (U : Set Worldsheet) :
    polyakovAction T g (fun _ => minkowskiMetric 2) X U
      = T / 2 * ∫ σ in U, (inducedMetric g X σ 0 0 - inducedMetric g X σ 1 1) := by sorry

end PolyakovAction
