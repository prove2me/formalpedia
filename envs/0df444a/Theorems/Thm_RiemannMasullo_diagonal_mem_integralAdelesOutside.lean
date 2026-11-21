-- Prove2me | Theorems.Thm_RiemannMasullo_diagonal_mem_integralAdelesOutside
-- name    : RiemannMasullo.diagonal_mem_integralAdelesOutside
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:44:20.898206+00:00
-- url     : https://prove2.me/theorems/effddee7-338d-4825-a6cb-0f154fa6b55c
-- title:
--   Diagonal S-integers in the adeles
-- statement:
--   A diagonal field element is integral outside a finite set S precisely when it is an S-integer.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L227-L232

import Mathlib
import Definitions.Def_RiemannMasullo_AdelicExtensions

open RiemannMasullo
open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct
variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)

namespace RiemannMasullo

theorem diagonal_mem_integralAdelesOutside (S : Finset (Primes(F))) (x : F) :
    algebraMap F 𝔸[F] x ∈ integralAdelesOutside F S ↔ x ∈ (S : Set (Primes(F))).integer F := by sorry

end RiemannMasullo
