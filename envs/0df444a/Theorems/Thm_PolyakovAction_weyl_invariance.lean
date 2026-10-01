-- Prove2me | Theorems.Thm_PolyakovAction_weyl_invariance
-- name    : PolyakovAction.weyl_invariance
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T10:09:27.584967+00:00
-- url     : https://prove2.me/theorems/189e7717-d1f6-4a8b-aaf3-aee2114e35f7
-- title:
--   Invariance under Weyl transformations
-- statement:
--   For every positive function $\Lambda(\sigma)>0$ on the worldsheet, the Weyl transformation $h_{ab}\to\tilde h_{ab}=\Lambda(\sigma)h_{ab}$ leaves the Polyakov action unchanged:
--   $$S[\Lambda h]=S[h].$$
--
--   In two dimensions $\tilde h^{ab}=\Lambda^{-1}h^{ab}$ and $\det\tilde h_{ab}=\Lambda^2\det h_{ab}$, so the factors cancel (source, "Weyl transformation").
--
--   **Formalization Note.** The Weyl factor is required to be positive, as for $\Lambda=e^{\phi}$; no other assumption on $h$, $X$ or $U$ is needed.
-- source:
--   Wikipedia, "Polyakov action", revision oldid=1292212311 (https://en.wikipedia.org/w/index.php?title=Polyakov_action&oldid=1292212311)

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

theorem weyl_invariance {D : ℕ} (T : ℝ) (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (Λ : Worldsheet → ℝ) (hΛ : ∀ σ, 0 < Λ σ) (U : Set Worldsheet) :
    polyakovAction T g (fun σ => Λ σ • h σ) X U = polyakovAction T g h X U := by sorry

end PolyakovAction
