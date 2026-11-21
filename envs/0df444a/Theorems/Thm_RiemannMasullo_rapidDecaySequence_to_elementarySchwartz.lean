-- Prove2me | Theorems.Thm_RiemannMasullo_rapidDecaySequence_to_elementarySchwartz
-- name    : RiemannMasullo.rapidDecaySequence_to_elementarySchwartz
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:12:33.432036+00:00
-- url     : https://prove2.me/theorems/cdeee103-7124-4717-9b71-e3ce3b1d259f
-- title:
--   Rapidly decreasing lattice sequences map continuously and injectively into the elementary Schwartz space
-- statement:
--   Reading a rapidly decreasing sequence as a function on the discrete elementary Lie group gives an injective continuous complex-linear map into its elementary Schwartz space.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L604-L606

import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
import Mathlib
open RiemannMasullo

namespace RiemannMasullo
theorem rapidDecaySequence_to_elementarySchwartz (r : ℕ) :
    ∃ L : RapidDecaySequence r →L[ℂ] ElementarySchwartz 0 0 r PUnit,
      Function.Injective L ∧ ∀ s (g : ElementaryLieGroup 0 0 r PUnit), L s g = s g.2.2.1 := by sorry
end RiemannMasullo
