-- Prove2me | Theorems.Thm_RiemannMasullo_rapidDecaySequenceSeminorm_zero
-- name    : RiemannMasullo.rapidDecaySequenceSeminorm_zero
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:42:32.828474+00:00
-- url     : https://prove2.me/theorems/2c0cc1be-73f2-4cb1-b94d-da94f7028ad2
-- title:
--   The zeroth sequence seminorm is the absolute sum
-- statement:
--   For each rapidly decreasing complex lattice sequence, the seminorm of order zero equals the sum of the absolute values.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L591-L592

import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}

namespace RiemannMasullo

theorem rapidDecaySequenceSeminorm_zero (s : RapidDecaySequence r) :
    rapidDecaySequenceSeminorm 0 s = ∑' a, ‖s a‖ := by sorry

end RiemannMasullo
