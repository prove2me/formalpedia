-- Prove2me | Theorems.Thm_RiemannMasullo_infiniteIdeleNorm_continuous
-- name    : RiemannMasullo.infiniteIdeleNorm_continuous
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:15:35.567316+00:00
-- url     : https://prove2.me/theorems/b908eb34-5a30-4b96-8a87-0d04471a089c
-- title:
--   Continuity of the archimedean idele norm
-- statement:
--   The product of the weighted archimedean norms is continuous on archimedean ideles.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L60-L61

import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

namespace RiemannMasullo

theorem infiniteIdeleNorm_continuous : Continuous (infiniteIdeleNorm F) := by sorry

end RiemannMasullo
