-- Prove2me | Theorems.Thm_RiemannMasullo_ratAdeleFundamentalDomain_precompact_translate
-- name    : RiemannMasullo.ratAdeleFundamentalDomain_precompact_translate
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:51:11.766196+00:00
-- url     : https://prove2.me/theorems/ac3a998b-1d6d-48c5-9455-cc52a64bd2c4
-- title:
--   Compact closure of every rational adelic fundamental-domain translate
-- statement:
--   For every rational q, the translate by the diagonal image of q of the standard rational adelic fundamental domain has compact closure.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L105-L107

import Mathlib
import Definitions.Def_RiemannMasullo_RationalAdeleFundamentalDomain
open NumberField InfinitePlace.Completion RiemannMasullo IsDedekindDomain
open scoped NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing Pointwise

namespace RiemannMasullo

theorem ratAdeleFundamentalDomain_precompact_translate (q : ℚ) :
    IsCompact (closure (algebraMap ℚ 𝔸[ℚ] q +ᵥ ratAdeleFundamentalDomain)) := by sorry

end RiemannMasullo
