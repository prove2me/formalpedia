-- Prove2me | Theorems.Thm_RiemannMasullo_rapidDecaySequence_isFrechet
-- name    : RiemannMasullo.rapidDecaySequence_isFrechet
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:58:22.129943+00:00
-- url     : https://prove2.me/theorems/901955be-6802-4766-a608-cfa1686892df
-- title:
--   Rapidly decreasing lattice sequences form a Fréchet space
-- statement:
--   The locally convex space of rapidly decreasing complex sequences on the integer lattice is metrizable and complete in its additive uniformity.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L600-L600

import Definitions.Def_RiemannMasullo_AppC_Nets_and_Bounded_Lifts
import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
open RiemannMasullo
variable {r : ℕ}

namespace RiemannMasullo

theorem rapidDecaySequence_isFrechet : IsFrechetTVS (RapidDecaySequence r) := by sorry

end RiemannMasullo
