-- Prove2me | Theorems.Thm_RiemannMasullo_infiniteIdeleLog_proper
-- name    : RiemannMasullo.infiniteIdeleLog_proper
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:31:20.663549+00:00
-- url     : https://prove2.me/theorems/e0906aee-5c11-4dac-9969-3c473917046b
-- title:
--   Properness of the archimedean idele logarithm
-- statement:
--   The preimage of every compact subset of the real logarithm coordinates is compact in the archimedean idele group.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L121-L122

import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

namespace RiemannMasullo

theorem infiniteIdeleLog_proper : IsProperMap (infiniteIdeleLog F) := by sorry

end RiemannMasullo
