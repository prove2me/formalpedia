-- Prove2me | Theorems.Thm_RiemannMasullo_infiniteIdeleLog_surjective
-- name    : RiemannMasullo.infiniteIdeleLog_surjective
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:15:35.380012+00:00
-- url     : https://prove2.me/theorems/1085e3fb-0b98-4645-a571-23c1b7a13c8b
-- title:
--   Surjectivity of the archimedean idele logarithm
-- statement:
--   Every tuple of real numbers indexed by the infinite places is the full logarithm of an archimedean idele.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L74-L75

import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

namespace RiemannMasullo

theorem infiniteIdeleLog_surjective : Surjective (infiniteIdeleLog F) := by sorry

end RiemannMasullo
