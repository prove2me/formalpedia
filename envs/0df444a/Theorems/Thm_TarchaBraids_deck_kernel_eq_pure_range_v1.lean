-- Prove2me | Theorems.Thm_TarchaBraids_deck_kernel_eq_pure_range_v1
-- name    : TarchaBraids.deck_kernel_eq_pure_range_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-22T04:32:17.570076+00:00
-- url     : https://prove2.me/theorems/b6437d29-79c3-420f-8264-7f43c6690378
-- title:
--   The deck-permutation kernel is the image of the pure braid group
-- statement:
--   For the ordered-to-unordered configuration quotient covering, the kernel of the strand-permutation homomorphism is exactly the range of the fundamental-group map from the ordered configuration space, hence the image of the pure braid group.
-- source:
--   The standard covering-space exact sequence for ordered and unordered configuration spaces, specialised using Mathlib's quotient-covering monodromy kernel theorem.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_endpoint_permutation_action_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem deck_kernel_eq_pure_range_v1 (n : ℕ)
    (hp : IsQuotientCoveringMap (configProj n) (Equiv.Perm (Fin n))) :
    (hp.fundamentalGroupToMulOpposite
      (⟨baseOrdered n, rfl⟩ : (configProj n) ⁻¹' {baseUnordered n})).ker =
    (FundamentalGroup.mapOfEq
      ⟨configProj n, hp.continuous⟩
      (show configProj n (baseOrdered n) = baseUnordered n from rfl)).range := by sorry

end TarchaBraids
