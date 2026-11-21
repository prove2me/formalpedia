-- Prove2me | Theorems.Thm_RiemannMasullo_infiniteIdeleLog_mul
-- name    : RiemannMasullo.infiniteIdeleLog_mul
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:15:41.723046+00:00
-- url     : https://prove2.me/theorems/d360891b-45d1-486b-96b9-2ea40819c196
-- title:
--   The full logarithm takes products to sums
-- statement:
--   The logarithm of the product of two archimedean ideles is the sum of their logarithms.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L78-L80

import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

namespace RiemannMasullo

theorem infiniteIdeleLog_mul (g h : 𝕀∞) :
    infiniteIdeleLog F (g * h) = infiniteIdeleLog F g + infiniteIdeleLog F h := by sorry

end RiemannMasullo
