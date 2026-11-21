-- Prove2me | Theorems.Thm_RiemannMasullo_rapidDecaySequenceSeminorm_neg
-- name    : RiemannMasullo.rapidDecaySequenceSeminorm_neg
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:38:17.181979+00:00
-- url     : https://prove2.me/theorems/de6e3e14-ea26-4bd8-a700-f96e8c27090c
-- title:
--   Negation preserves the weighted lattice-sequence seminorm
-- statement:
--   Every weighted absolute sum is invariant under negation of the sequence.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L568-L570

import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceSubmodule
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}

namespace RiemannMasullo

theorem rapidDecaySequenceSeminorm_neg (j : ℕ) (s : rapidDecaySequenceSubmodule r) :
    (rapidDecaySequenceBound j (-s).val).toReal = (rapidDecaySequenceBound j s.val).toReal := by sorry

end RiemannMasullo
