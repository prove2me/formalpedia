-- Prove2me | Theorems.Thm_RiemannMasullo_rapidDecaySequenceSubmodule_smul_mem
-- name    : RiemannMasullo.rapidDecaySequenceSubmodule_smul_mem
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:24:26.371558+00:00
-- url     : https://prove2.me/theorems/fd96ad50-903b-4ed5-b59f-55d962fb8e61
-- title:
--   Rapidly decreasing lattice sequences are closed under complex scaling
-- statement:
--   Every complex multiple of a lattice sequence with finite weighted sums has finite weighted sums.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L531-L533

import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceBound
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}

namespace RiemannMasullo

theorem rapidDecaySequenceSubmodule_smul_mem (c : ℂ) {s : (Fin r → ℤ) → ℂ}
    (hs : ∀ j, rapidDecaySequenceBound j s < ⊤) :
    ∀ j, rapidDecaySequenceBound j (c • s) < ⊤ := by sorry

end RiemannMasullo
