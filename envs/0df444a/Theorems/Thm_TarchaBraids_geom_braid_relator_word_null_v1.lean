-- Prove2me | Theorems.Thm_TarchaBraids_geom_braid_relator_word_null_v1
-- name    : TarchaBraids.geom_braid_relator_word_null_v1
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-27T21:03:42.855979+00:00
-- url     : https://prove2.me/theorems/1e2d1635-cd71-47a4-8241-68898a9072fe
-- title:
--   Every Artin relator word is null in the geometric braid group
-- statement:
--   Assembly of the two diagram-move lemmas for Tarcha's Theorem 3.15 (Figures 3.18--3.22). The set braidRels n of Artin defining relations is exactly the union of the far-commuting relator words and the adjacent braid relator words (Definitions.Def_BraidsLinksMCG_ArtinBraidGroup), so membership of r in braidRels n yields that r evaluates to the identity under FreeGroup.lift (halfTwistBraid n). This is the diagram-move certificate package consumed by the finite contextual relator trace construction of TarchaBraids.geom_null_word_has_contextual_relator_trace_v1.
-- source:
--   Tarcha, Um Estudo Introdutorio da Teoria de Trancas, Theorem 3.15, pp. 59--62, Figures 3.18--3.27; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

/-- Every Artin relator word is geometrically null: the diagram-move
    certificate package for the finite-trace construction. -/
theorem geom_braid_relator_word_null_v1 (n : ℕ) (r : FreeGroup (Fin (n - 1)))
    (hr : r ∈ BraidsLinksMCG.braidRels n) :
    FreeGroup.lift (halfTwistBraid n) r = 1 := by
  sorry

end TarchaBraids
