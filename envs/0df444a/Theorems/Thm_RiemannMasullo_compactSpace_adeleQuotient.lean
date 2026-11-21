-- Prove2me | Theorems.Thm_RiemannMasullo_compactSpace_adeleQuotient
-- name    : RiemannMasullo.compactSpace_adeleQuotient
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:53:15.70319+00:00
-- url     : https://prove2.me/theorems/60762696-6710-487f-af0c-82ede5add191
-- title:
--   Compactness of the additive adele class group
-- statement:
--   The additive topological quotient of the adele ring of a number field by its diagonal field is compact.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L507-L546

import Mathlib
open Function NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
local notation "Principal(" F ")" => AdeleRing.principalSubgroup (𝓞 F) F
local notation "AQuot(" F ")" => 𝔸[F] ⧸ Principal(F)

namespace RiemannMasullo
theorem compactSpace_adeleQuotient : CompactSpace (AQuot(F)) := by sorry
end RiemannMasullo
