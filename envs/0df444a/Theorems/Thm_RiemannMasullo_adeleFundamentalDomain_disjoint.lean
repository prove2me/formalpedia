-- Prove2me | Theorems.Thm_RiemannMasullo_adeleFundamentalDomain_disjoint
-- name    : RiemannMasullo.adeleFundamentalDomain_disjoint
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:34:04.218281+00:00
-- url     : https://prove2.me/theorems/20435d14-92d4-4c8e-97ce-b728885bb773
-- title:
--   Distinct diagonal translates of the adelic fundamental domain are disjoint
-- statement:
--   Translation by any nonzero diagonal element of the field moves the fundamental domain off itself.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L75-L77

import Mathlib
import Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
open RiemannMasullo
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
variable {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))

namespace RiemannMasullo

theorem adeleFundamentalDomain_disjoint (x : F) (hx : x ≠ 0) :
    Disjoint (algebraMap F 𝔸[F] x +ᵥ adeleFundamentalDomain F b) (adeleFundamentalDomain F b) := by sorry

end RiemannMasullo
