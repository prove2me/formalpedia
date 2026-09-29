-- Prove2me | Theorems.Thm_TarchaBraids_geom_braid_far_relator_word_null_v1
-- name    : TarchaBraids.geom_braid_far_relator_word_null_v1
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-27T21:03:46.425047+00:00
-- url     : https://prove2.me/theorems/231d713e-509a-4d65-81a3-8e20d791fbb9
-- title:
--   The far-commuting Artin relator word is null in the geometric braid group
-- statement:
--   Diagram-move lemma for Tarcha's Theorem 3.15 (Figures 3.18--3.19). The elementary geometric half-twists about strands i and j with |i - j| >= 2 have disjoint supports, so they commute as loops in the unordered configuration space; hence the commuting Artin relator word (FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)^{-1} * (FreeGroup.of j)^{-1}) evaluates to the identity under FreeGroup.lift (halfTwistBraid n). This is the commuting half of the claim that every Artin relator word is geometrically null, an input to TarchaBraids.geom_null_word_has_contextual_relator_trace_v1.
-- source:
--   Tarcha, Um Estudo Introdutorio da Teoria de Trancas, Theorem 3.15, pp. 59--62, Figures 3.18--3.27; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

/-- Figures 3.18--3.19: the far-commuting relator word evaluates to `1`. -/
theorem geom_braid_far_relator_word_null_v1 (n : ℕ) (i j : Fin (n - 1))
    (h : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    FreeGroup.lift (halfTwistBraid n)
      (FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹) = 1 := by
  sorry

end TarchaBraids
