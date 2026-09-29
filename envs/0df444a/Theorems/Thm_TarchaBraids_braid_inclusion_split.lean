-- Prove2me | Theorems.Thm_TarchaBraids_braid_inclusion_split
-- name    : TarchaBraids.braid_inclusion_split
-- status  : Disproved
-- author  : @junyihjy
-- created : 2026-09-21T15:06:44.703717+00:00
-- url     : https://prove2.me/theorems/304074fc-9085-4c2f-9a4c-ece8d7ad6b5e
-- statement:
--   For m <= n, the generator map sigma_i -> sigma_i extends to a homomorphism B_m -> B_n admitting a retraction B_n -> B_m.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

namespace TarchaBraids

open BraidsLinksMCG

theorem braid_inclusion_split {m n : Nat} (h : m <= n) :
    Exists (fun f : MonoidHom (ArtinBraidGroup m) (ArtinBraidGroup n) =>
      (forall i : Fin (m - 1), f (sigma i) = sigma (Fin.castLE (Nat.sub_le_sub_right h 1) i))
      /\ Exists (fun g : MonoidHom (ArtinBraidGroup n) (ArtinBraidGroup m) =>
        forall x, g (f x) = x)) := by sorry

end TarchaBraids
