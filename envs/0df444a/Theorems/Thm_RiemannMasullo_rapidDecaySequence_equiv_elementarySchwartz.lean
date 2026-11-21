-- Prove2me | Theorems.Thm_RiemannMasullo_rapidDecaySequence_equiv_elementarySchwartz
-- name    : RiemannMasullo.rapidDecaySequence_equiv_elementarySchwartz
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:19:19.289034+00:00
-- url     : https://prove2.me/theorems/08f06329-8bab-4f3b-9fa9-a64d1492e0c0
-- title:
--   Rapidly decreasing sequences and elementary Schwartz functions on the integer lattice are topologically isomorphic
-- statement:
--   Evaluation identifies the rapidly decreasing complex sequences of rank r with the elementary Schwartz functions on the integer lattice, as complex locally convex spaces.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L604-L606

import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
import Mathlib
open RiemannMasullo
variable {r : ℕ}

namespace RiemannMasullo

theorem rapidDecaySequence_equiv_elementarySchwartz :
    ∃ e : RapidDecaySequence r ≃L[ℂ] ElementarySchwartz 0 0 r PUnit,
      ∀ s (g : ElementaryLieGroup 0 0 r PUnit), e s g = s g.2.2.1 := by sorry

end RiemannMasullo
