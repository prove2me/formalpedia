-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_half_twists_braid_relation
-- name    : TarchaBraids.thm_3_15_half_twists_braid_relation
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T03:02:44.099445+00:00
-- url     : https://prove2.me/theorems/52e4f20f-65f1-4f8f-9d32-d9095b3e0d37
-- title:
--   Braid relation for adjacent half-twists
-- statement:
--   In the geometric braid group $\pi_1(B_{0,n}E^2)$, let $\mathrm{ht}_i$ denote the class of the elementary half-twist interchanging the $i$-th and $(i+1)$-st base points. Adjacent half-twists satisfy the braid relation:
--
--   $$[\mathrm{ht}_i][\mathrm{ht}_{i+1}][\mathrm{ht}_i]=[\mathrm{ht}_{i+1}][\mathrm{ht}_i][\mathrm{ht}_{i+1}].$$
--
--   This is the second of Artin's two defining relation families. Unlike the commutation relation, the two sides here involve half-twists with overlapping supports, and the identity expresses that the two ways of cyclically permuting three adjacent punctures are isotopic. It is the relation that makes the braid group non-abelian and is the substantive half of the verification that the half-twists satisfy Artin's presentation.
--
--   It is stated separately from the commutation relation because the two are established by different geometric arguments.
-- source:
--   Tarcha, Braid Theory and the Artin Presentation, Teorema 3.15 (first half), which verifies that the half-twist classes satisfy Artin's defining relations; cf. Birman, Braids, Links and Mapping Class Groups, Ch. 1, equations (1-1) and (1-2). The two relation families are checked by separate geometric arguments and are stated here as separate lemmas.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_half_twists_braid_relation (n : ℕ) :
    ∀ i j : Fin (n - 1), (j : ℕ) = (i : ℕ) + 1 →
      halfTwistBraid n i * halfTwistBraid n j * halfTwistBraid n i =
        halfTwistBraid n j * halfTwistBraid n i * halfTwistBraid n j := by sorry

end TarchaBraids
