-- Prove2me | Theorems.Thm_TarchaBraids_braid_corrects_to_pure_range_of_quotient_v1
-- name    : TarchaBraids.braid_corrects_to_pure_range_of_quotient_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-22T08:23:24.491522+00:00
-- url     : https://prove2.me/theorems/32ef1764-54ce-4a34-8b84-c005b00dc4b8
-- title:
--   Permutation correction leaves a pure braid for the configuration quotient covering
-- statement:
--   For any symmetric-group quotient-covering structure on the ordered-to-unordered configuration projection, every geometric braid can be corrected by the inverse of a word in the explicit elementary half-twists so that the residual braid lies in the image of the ordered-configuration fundamental group. Equivalently, after matching its strand permutation by adjacent half-twists, the remaining braid is pure.
-- source:
--   Tarcha Teorema 3.11 exact-sequence reduction: match the strand permutation by an adjacent half-twist word, leaving an element of the pure-braid kernel.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_endpoint_permutation_action_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem braid_corrects_to_pure_range_of_quotient_v1 (n : ℕ)
    (hp : IsQuotientCoveringMap (configProj n) (Equiv.Perm (Fin n)))
    (β : GeomBraidGroup n) :
    ∃ w : FreeGroup (Fin (n - 1)),
      β * (FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i) w)⁻¹ ∈
        (FundamentalGroup.mapOfEq
          ⟨configProj n, hp.continuous⟩
          (show configProj n (baseOrdered n) = baseUnordered n from rfl)).range := by sorry

end TarchaBraids
