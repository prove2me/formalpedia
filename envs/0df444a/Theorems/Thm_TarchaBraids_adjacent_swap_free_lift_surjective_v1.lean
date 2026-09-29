-- Prove2me | Theorems.Thm_TarchaBraids_adjacent_swap_free_lift_surjective_v1
-- name    : TarchaBraids.adjacent_swap_free_lift_surjective_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T22:55:49.769538+00:00
-- url     : https://prove2.me/theorems/a9707ad6-7359-4f54-a57a-097e3633f9c9
-- title:
--   Adjacent transpositions give a surjective free-group lift to the symmetric group
-- statement:
--   For m + 1 labelled strands, every endpoint permutation is represented by a signed word in the m adjacent transpositions. Equivalently, the free-group homomorphism sending generator i to the adjacent swap of i and i+1 is surjective onto the full permutation group.
-- source:
--   Tarcha Teorema 3.11 endpoint-permutation correction, together with the standard fact that adjacent transpositions generate the finite symmetric group.

import Mathlib

namespace TarchaBraids

theorem adjacent_swap_free_lift_surjective_v1 (m : ℕ) :
    Function.Surjective
      (FreeGroup.lift
        (fun i : Fin m =>
          (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (m + 1))))) := by sorry

end TarchaBraids
