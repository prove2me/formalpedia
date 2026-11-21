-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartz_t2
-- name    : RiemannMasullo.elementarySchwartz_t2
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:17:09.872179+00:00
-- url     : https://prove2.me/theorems/078fbd2b-91ed-4795-b483-048c9e1e6399
-- title:
--   The elementary Schwartz topology is Hausdorff
-- statement:
--   Any two distinct elementary Schwartz functions admit disjoint open neighbourhoods for the topology defined by the weighted derivative seminorms.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L439-L439

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

namespace RiemannMasullo

theorem elementarySchwartz_t2 : T2Space (ElementarySchwartz m n r F) := by sorry

end RiemannMasullo
