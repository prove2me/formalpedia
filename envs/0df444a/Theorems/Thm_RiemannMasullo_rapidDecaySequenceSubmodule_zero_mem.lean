-- Prove2me | Theorems.Thm_RiemannMasullo_rapidDecaySequenceSubmodule_zero_mem
-- name    : RiemannMasullo.rapidDecaySequenceSubmodule_zero_mem
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:24:25.625889+00:00
-- url     : https://prove2.me/theorems/51d12c12-5ddb-4202-ba14-622a37007a09
-- title:
--   The zero sequence is rapidly decreasing
-- statement:
--   The zero sequence on the integer lattice has finite weighted sums of every order.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L519-L520

import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceBound
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}

namespace RiemannMasullo

theorem rapidDecaySequenceSubmodule_zero_mem :
    ∀ j, rapidDecaySequenceBound j (0 : (Fin r → ℤ) → ℂ) < ⊤ := by sorry

end RiemannMasullo
