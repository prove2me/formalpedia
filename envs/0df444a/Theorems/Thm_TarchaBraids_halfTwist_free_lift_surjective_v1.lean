-- Prove2me | Theorems.Thm_TarchaBraids_halfTwist_free_lift_surjective_v1
-- name    : TarchaBraids.halfTwist_free_lift_surjective_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-21T18:13:14.70081+00:00
-- url     : https://prove2.me/theorems/39530bb2-1531-44c0-bd02-e2da5b5e200e
-- title:
--   Every geometric braid is a free word in the elementary half-twists
-- statement:
--   Every geometric braid is represented by a finite word in the elementary half-twists and their inverses. Equivalently, the homomorphism from the free group on the Artin generator indices to the geometric braid group, sending each free generator to its explicit half-twist class, is surjective.
-- source:
--   Tarcha Teorema 3.11: partition a geometric braid into finitely many one-crossing slabs, each equivalent to an Artin generator or its inverse.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem halfTwist_free_lift_surjective_v1 (n : ℕ) :
    Function.Surjective
      (FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i)) := by sorry

end TarchaBraids
