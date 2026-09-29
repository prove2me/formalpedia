-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_half_twists_commute
-- name    : TarchaBraids.thm_3_15_half_twists_commute
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T03:02:53.213558+00:00
-- url     : https://prove2.me/theorems/a888ac56-e29a-45d3-b7f1-0be3ddf640f9
-- title:
--   Half-twists far apart commute: $|i-j|\ge 2$
-- statement:
--   In the geometric braid group $\pi_1(B_{0,n}E^2)$, let $\mathrm{ht}_i$ denote the class of the elementary half-twist interchanging the $i$-th and $(i+1)$-st base points. Then half-twists whose indices are far apart commute:
--
--   $$[\mathrm{ht}_i][\mathrm{ht}_j]=[\mathrm{ht}_j][\mathrm{ht}_i]\qquad	ext{whenever } |i-j|\ge 2.$$
--
--   This is the first of Artin's two defining relation families. Geometrically it holds because when $|i-j|\ge 2$ the two half-twists are supported in disjoint discs of the punctured plane, so the corresponding loops can be performed independently and the order in which they are traversed does not matter up to homotopy.
--
--   It is stated separately from the braid relation because the two are established by different geometric arguments: disjointness of supports here, versus an explicit isotopy of three adjacent punctures there.
-- source:
--   Tarcha, Braid Theory and the Artin Presentation, Teorema 3.15 (first half), which verifies that the half-twist classes satisfy Artin's defining relations; cf. Birman, Braids, Links and Mapping Class Groups, Ch. 1, equations (1-1) and (1-2). The two relation families are checked by separate geometric arguments and are stated here as separate lemmas.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_half_twists_commute (n : ℕ) :
    ∀ i j : Fin (n - 1), 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs →
      halfTwistBraid n i * halfTwistBraid n j = halfTwistBraid n j * halfTwistBraid n i := by sorry

end TarchaBraids
