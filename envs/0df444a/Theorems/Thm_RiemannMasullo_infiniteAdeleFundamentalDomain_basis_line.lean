-- Prove2me | Theorems.Thm_RiemannMasullo_infiniteAdeleFundamentalDomain_basis_line
-- name    : RiemannMasullo.infiniteAdeleFundamentalDomain_basis_line
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:30:28.224654+00:00
-- url     : https://prove2.me/theorems/302b3b62-b519-4232-8a6e-3e21e6a93e09
-- title:
--   A basis line in the infinite adelic fundamental domain
-- statement:
--   The multiple t of a Minkowski basis vector lies in the half-open fundamental domain exactly for 0 ≤ t < 1.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L48-L51

import Mathlib
import Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
open RiemannMasullo
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
variable {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))

namespace RiemannMasullo

theorem infiniteAdeleFundamentalDomain_basis_line (i : ι) (t : ℝ) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • mixedEmbedding F (b i : F)) ∈
      infiniteAdeleFundamentalDomain F b ↔ t ∈ Set.Ico 0 1 := by sorry

end RiemannMasullo
