-- Prove2me | Theorems.Thm_RiemannMasullo_exists_sub_diagonal_mem_integralAdeles
-- name    : RiemannMasullo.exists_sub_diagonal_mem_integralAdeles
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:35:10.426677+00:00
-- url     : https://prove2.me/theorems/36f5c63d-2cdb-471e-b81f-0011003b5433
-- title:
--   Every adele is integral at all finite places after diagonal translation
-- statement:
--   For every adele a there exists a field element x such that subtracting its diagonal image from a leaves every finite component integral.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L343-L407

import Mathlib
import Definitions.Def_RiemannMasullo_AdelicExtensions

open RiemannMasullo
open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct
variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)

local notation "Integral(" F ")" => integralAdelesOutside F ∅

namespace RiemannMasullo
theorem exists_sub_diagonal_mem_integralAdeles (a : 𝔸[F]) :
    ∃ x : F, a - algebraMap F 𝔸[F] x ∈ Integral(F) := by sorry
end RiemannMasullo
