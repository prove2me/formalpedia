-- Prove2me | Theorems.Thm_RiemannMasullo_adeleFundamentalDomain_precompact
-- name    : RiemannMasullo.adeleFundamentalDomain_precompact
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:31:22.305548+00:00
-- url     : https://prove2.me/theorems/561f513d-637d-4420-b875-e9c7d93b8af2
-- title:
--   Compact closure of the adelic fundamental domain
-- statement:
--   The half-open adelic fundamental domain attached to an integral basis has compact closure.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L66-L67

import Mathlib
import Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
open RiemannMasullo
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]
variable {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))

namespace RiemannMasullo

theorem adeleFundamentalDomain_precompact : IsCompact (closure (adeleFundamentalDomain F b)) := by sorry

end RiemannMasullo
