-- Prove2me | Theorems.Thm_RiemannMasullo_mem_rapidDecaySequenceSubmodule_of_finiteSupport
-- name    : RiemannMasullo.mem_rapidDecaySequenceSubmodule_of_finiteSupport
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:38:20.722114+00:00
-- url     : https://prove2.me/theorems/55cd060c-78f4-49b7-8f3d-168f8883e41f
-- title:
--   Finitely supported lattice sequences are rapidly decreasing
-- statement:
--   Every finitely supported complex sequence on the integer lattice has finite weighted absolute sum of every order.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L545-L547

import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceSubmodule
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}

namespace RiemannMasullo

theorem mem_rapidDecaySequenceSubmodule_of_finiteSupport (s : (Fin r → ℤ) → ℂ)
    (hs : (Function.support s).Finite) :
    s ∈ rapidDecaySequenceSubmodule r := by sorry

end RiemannMasullo
