-- Prove2me | Theorems.Thm_RiemannMasullo_infiniteIdeleNorm_ker_closed
-- name    : RiemannMasullo.infiniteIdeleNorm_ker_closed
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:15:41.76923+00:00
-- url     : https://prove2.me/theorems/b0b6406c-3423-40bb-828d-d334289e2727
-- title:
--   Closedness of the norm-one archimedean ideles
-- statement:
--   Archimedean ideles of norm one form a closed subgroup.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L64-L65

import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

namespace RiemannMasullo

theorem infiniteIdeleNorm_ker_closed : IsClosed (N∞ : Set 𝕀∞) := by sorry

end RiemannMasullo
