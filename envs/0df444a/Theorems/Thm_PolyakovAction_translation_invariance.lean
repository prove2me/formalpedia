-- Prove2me | Theorems.Thm_PolyakovAction_translation_invariance
-- name    : PolyakovAction.translation_invariance
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-01T03:36:40.393988+00:00
-- url     : https://prove2.me/theorems/ea45dff1-5dde-4fd0-be81-34ba330b2237
-- title:
--   Invariance under spacetime translations
-- statement:
--   Let the target metric be a constant matrix $g_{\mu\nu}$. For every constant vector $b^\alpha$, the spacetime translation $X^\alpha\to X^\alpha+b^\alpha$ leaves the Polyakov action unchanged:
--   $$S[X+b]=S[X].$$
--
--   This is transformation (i) of the Poincaré symmetry of the target manifold in the source ("Global symmetries"); it holds because the action depends on $X$ only through its first derivatives.
--
--   **Formalization Note.** The target metric is taken constant (flat target), the setting in which the source's Poincaré symmetry is stated. The identity holds for any worldsheet metric, any region and any map $X$.
-- source:
--   Wikipedia, "Polyakov action", revision oldid=1292212311 (https://en.wikipedia.org/w/index.php?title=Polyakov_action&oldid=1292212311)

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

theorem translation_invariance {D : ℕ} (T : ℝ) (g : Matrix (Fin D) (Fin D) ℝ)
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (b : Spacetime D) (U : Set Worldsheet) :
    polyakovAction T (fun _ => g) h (fun σ => X σ + b) U
      = polyakovAction T (fun _ => g) h X U := by sorry

end PolyakovAction
