-- Prove2me | Theorems.Thm_RiemannMasullo_rapidDecaySequenceSubmodule_add_mem
-- name    : RiemannMasullo.rapidDecaySequenceSubmodule_add_mem
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:24:27.395832+00:00
-- url     : https://prove2.me/theorems/729cb469-1509-460d-8c24-8e53dfda4ddf
-- title:
--   Rapidly decreasing lattice sequences are closed under addition
-- statement:
--   The sum of two lattice sequences with finite weighted sums at every order has the same property.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L524-L527

import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceBound
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}

namespace RiemannMasullo

theorem rapidDecaySequenceSubmodule_add_mem {s t : (Fin r → ℤ) → ℂ}
    (hs : ∀ j, rapidDecaySequenceBound j s < ⊤)
    (ht : ∀ j, rapidDecaySequenceBound j t < ⊤) :
    ∀ j, rapidDecaySequenceBound j (s + t) < ⊤ := by sorry

end RiemannMasullo
