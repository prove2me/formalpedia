-- Prove2me | Theorems.Thm_RiemannMasullo_rapidDecaySequenceSeminorm_add_le
-- name    : RiemannMasullo.rapidDecaySequenceSeminorm_add_le
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:38:15.488179+00:00
-- url     : https://prove2.me/theorems/b54532d2-a39e-4446-a4a1-9950565ffd87
-- title:
--   Subadditivity of weighted lattice-sequence seminorms
-- statement:
--   Each real-valued weighted absolute sum satisfies the triangle inequality on rapidly decreasing sequences.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L555-L558

import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceSubmodule
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}

namespace RiemannMasullo

theorem rapidDecaySequenceSeminorm_add_le (j : ℕ) (s t : rapidDecaySequenceSubmodule r) :
    (rapidDecaySequenceBound j (s + t).val).toReal ≤
      (rapidDecaySequenceBound j s.val).toReal + (rapidDecaySequenceBound j t.val).toReal := by sorry

end RiemannMasullo
