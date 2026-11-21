-- Prove2me | Theorems.Thm_RiemannMasullo_rapidDecaySequenceSeminorm_map_zero
-- name    : RiemannMasullo.rapidDecaySequenceSeminorm_map_zero
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:38:20.460928+00:00
-- url     : https://prove2.me/theorems/a86835a8-b6ad-4bf9-8db6-82465094e55b
-- title:
--   Every weighted lattice-sequence seminorm vanishes at zero
-- statement:
--   The real-valued weighted absolute sum of the zero sequence is zero.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L550-L551

import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceSubmodule
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}

namespace RiemannMasullo

theorem rapidDecaySequenceSeminorm_map_zero (j : ℕ) :
    (rapidDecaySequenceBound j (0 : rapidDecaySequenceSubmodule r).val).toReal = 0 := by sorry

end RiemannMasullo
