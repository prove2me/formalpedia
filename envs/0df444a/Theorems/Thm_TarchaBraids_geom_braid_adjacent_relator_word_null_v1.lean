-- Prove2me | Theorems.Thm_TarchaBraids_geom_braid_adjacent_relator_word_null_v1
-- name    : TarchaBraids.geom_braid_adjacent_relator_word_null_v1
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-27T21:03:48.997439+00:00
-- url     : https://prove2.me/theorems/b033f15c-8be8-4aa0-8053-7a7b79cc7621
-- title:
--   The adjacent braid relator word is null in the geometric braid group
-- statement:
--   Diagram-move lemma for Tarcha's Theorem 3.15 (Figures 3.20--3.22): the three-strand braid move. The elementary geometric half-twists satisfy the adjacent braid relation as loops in the unordered configuration space, so the adjacent Artin relator word (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i * (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)^{-1}), for j = i + 1, evaluates to the identity under FreeGroup.lift (halfTwistBraid n). This is the braid half of the claim that every Artin relator word is geometrically null, an input to TarchaBraids.geom_null_word_has_contextual_relator_trace_v1.
-- source:
--   Tarcha, Um Estudo Introdutorio da Teoria de Trancas, Theorem 3.15, pp. 59--62, Figures 3.18--3.27; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

/-- Figures 3.20--3.22: the adjacent braid relator word evaluates to `1`. -/
theorem geom_braid_adjacent_relator_word_null_v1 (n : ℕ) (i j : Fin (n - 1))
    (h : (j : ℕ) = (i : ℕ) + 1) :
    FreeGroup.lift (halfTwistBraid n)
      (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
        (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹) = 1 := by
  sorry

end TarchaBraids
