-- Prove2me | Theorems.Thm_RiemannMasullo_adeleQuotient_nsmul_bijective
-- name    : RiemannMasullo.adeleQuotient_nsmul_bijective
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:53:16.652487+00:00
-- url     : https://prove2.me/theorems/2ac887f9-cbd0-4ce7-9ece-9df81625fa1b
-- title:
--   Unique divisibility of the additive adele class group
-- statement:
--   Multiplication by any positive natural number is bijective on the additive adeles modulo the diagonal field.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L449-L476

import Mathlib
open Function NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
local notation "Principal(" F ")" => AdeleRing.principalSubgroup (𝓞 F) F
local notation "AQuot(" F ")" => 𝔸[F] ⧸ Principal(F)

namespace RiemannMasullo
theorem adeleQuotient_nsmul_bijective (n : ℕ) (hn : 0 < n) :
    Bijective (fun x : AQuot(F) ↦ n • x) := by sorry
end RiemannMasullo
