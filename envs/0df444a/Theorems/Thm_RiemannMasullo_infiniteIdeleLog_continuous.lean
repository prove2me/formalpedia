-- Prove2me | Theorems.Thm_RiemannMasullo_infiniteIdeleLog_continuous
-- name    : RiemannMasullo.infiniteIdeleLog_continuous
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:15:34.065122+00:00
-- url     : https://prove2.me/theorems/6c45219b-b68c-4719-83a8-8b7bb882aec5
-- title:
--   Continuity of the full archimedean logarithm
-- statement:
--   The full logarithm of an archimedean idele is continuous in the product topology.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L83-L84

import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

namespace RiemannMasullo

theorem infiniteIdeleLog_continuous : Continuous (infiniteIdeleLog F) := by sorry

end RiemannMasullo
