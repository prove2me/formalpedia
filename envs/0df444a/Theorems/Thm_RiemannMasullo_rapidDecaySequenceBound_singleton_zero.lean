-- Prove2me | Theorems.Thm_RiemannMasullo_rapidDecaySequenceBound_singleton_zero
-- name    : RiemannMasullo.rapidDecaySequenceBound_singleton_zero
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:24:26.973548+00:00
-- url     : https://prove2.me/theorems/78416e55-938a-4be1-a5a0-c56886c8ab91
-- title:
--   The weighted sum of a point mass at the origin
-- statement:
--   For every weight, a point mass at the origin has weighted absolute sum equal to the norm of its coefficient.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L513-L515

import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceBound
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}

namespace RiemannMasullo

theorem rapidDecaySequenceBound_singleton_zero (j : ℕ) (c : ℂ) :
    rapidDecaySequenceBound (r := r) j (({0} : Set (Fin r → ℤ)).indicator (fun _ ↦ c)) =
      (‖c‖₊ : ℝ≥0∞) := by sorry

end RiemannMasullo
