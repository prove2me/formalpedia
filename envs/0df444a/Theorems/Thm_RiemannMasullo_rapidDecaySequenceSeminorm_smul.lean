-- Prove2me | Theorems.Thm_RiemannMasullo_rapidDecaySequenceSeminorm_smul
-- name    : RiemannMasullo.rapidDecaySequenceSeminorm_smul
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:38:01.620731+00:00
-- url     : https://prove2.me/theorems/c283ae3d-d21a-4515-adf0-44c3102260dc
-- title:
--   Absolute homogeneity of weighted lattice-sequence seminorms
-- statement:
--   Complex scaling multiplies the weighted seminorm of a rapidly decreasing sequence by the norm of the scalar.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L562-L564

import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceSubmodule
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}

namespace RiemannMasullo

theorem rapidDecaySequenceSeminorm_smul (j : ℕ) (c : ℂ) (s : rapidDecaySequenceSubmodule r) :
    (rapidDecaySequenceBound j (c • s).val).toReal =
      ‖c‖ * (rapidDecaySequenceBound j s.val).toReal := by sorry

end RiemannMasullo
