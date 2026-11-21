-- Prove2me | Theorems.Thm_RiemannMasullo_adeleFundamentalDomain_finite_translates
-- name    : RiemannMasullo.adeleFundamentalDomain_finite_translates
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:39:14.843103+00:00
-- url     : https://prove2.me/theorems/2eac4311-4ac8-4518-9c3e-4ed756333bb8
-- title:
--   Only finitely many fundamental-domain closures meet a compact set
-- statement:
--   For any compact set of adeles, only finitely many diagonal field translates of the closed fundamental domain meet it.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L87-L89

import Mathlib
import Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
open RiemannMasullo
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
variable {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))

namespace RiemannMasullo

theorem adeleFundamentalDomain_finite_translates (K : Set 𝔸[F]) (hK : IsCompact K) :
    {x : F | ((algebraMap F 𝔸[F] x +ᵥ closure (adeleFundamentalDomain F b)) ∩ K).Nonempty}.Finite := by sorry

end RiemannMasullo
