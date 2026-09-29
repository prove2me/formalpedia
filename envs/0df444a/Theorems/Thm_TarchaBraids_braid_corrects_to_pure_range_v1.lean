-- Prove2me | Theorems.Thm_TarchaBraids_braid_corrects_to_pure_range_v1
-- name    : TarchaBraids.braid_corrects_to_pure_range_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-22T06:56:14.657507+00:00
-- url     : https://prove2.me/theorems/269944ea-9059-4878-8e53-ee5de51e7c78
-- title:
--   Every braid is a half-twist word times a pure braid
-- statement:
--   Every geometric braid can be corrected by the inverse of a word in the explicit elementary half-twists so that the residual braid lies in the image of the ordered-configuration fundamental group, i.e. is pure. This combines adjacent-permutation generation, the explicit deck permutation of each half-twist, permutation correction to the deck kernel, and identification of that kernel with the pure-braid image.
-- source:
--   Tarcha Teorema 3.11 exact-sequence reduction: match the strand permutation by an adjacent half-twist word, leaving a pure braid.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_configProj_isQuotientCoveringMap_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem braid_corrects_to_pure_range_v1 (n : ℕ) (β : GeomBraidGroup n) :
    ∃ w : FreeGroup (Fin (n - 1)),
      β * (FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i) w)⁻¹ ∈
        (FundamentalGroup.mapOfEq
          ⟨configProj n, (configProj_isQuotientCoveringMap_v1 n).continuous⟩
          (show configProj n (baseOrdered n) = baseUnordered n from rfl)).range := by sorry

end TarchaBraids
