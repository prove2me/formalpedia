-- Prove2me | Theorems.Thm_RiemannMasullo_isDiscrete_principalAdeles
-- name    : RiemannMasullo.isDiscrete_principalAdeles
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:37:54.80679+00:00
-- url     : https://prove2.me/theorems/1bec7210-a878-4f48-8699-fd11f5722802
-- title:
--   The diagonal field forms a discrete subgroup of the adeles
-- statement:
--   The additive subgroup of principal adeles of a number field is discrete in the adelic topology.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L298-L340

import Mathlib
import Definitions.Def_RiemannMasullo_AdelicExtensions

open RiemannMasullo
open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct
variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)

local notation "Integral(" F ")" => integralAdelesOutside F ∅

local notation "Principal(" F ")" => AdeleRing.principalSubgroup (𝓞 F) F

namespace RiemannMasullo
theorem isDiscrete_principalAdeles : IsDiscrete (Principal(F) : Set 𝔸[F]) := by sorry
end RiemannMasullo
