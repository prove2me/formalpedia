-- Prove2me | Theorems.Thm_TarchaBraids_geom_braid_to_artin_word_hom_v1
-- name    : TarchaBraids.geom_braid_to_artin_word_hom_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T22:45:00.336582+00:00
-- url     : https://prove2.me/theorems/32dc6fb0-1816-4a56-9f36-57b09bf44d3d
-- title:
--   Geometric braid classes have an Artin word homomorphism matching half-twists
-- statement:
--   A loop of unordered configurations determines an Artin braid word class. The assignment respects concatenation of loops and homotopy, giving a homomorphism from the geometric braid group to the abstract braid group. For every elementary geometric half-twist, the resulting class is the corresponding abstract generator. This is the braid-diagram word assignment in the injectivity argument of Tarcha's Theorem 3.15; its construction is independent of an action on the punctured-plane fundamental group.
-- source:
--   Tarcha, Braid Theory and the Artin Presentation, Theorem 3.15, elementary moves in braid diagrams (Figures 3.18-3.27); Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem geom_braid_to_artin_word_hom_v1 (n : ℕ) :
    ∃ g : GeomBraidGroup n →* ArtinBraidGroup n,
      ∀ i : Fin (n - 1), g (halfTwistBraid n i) = sigma i := by sorry

end TarchaBraids
