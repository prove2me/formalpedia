-- Prove2me | Theorems.Thm_TarchaBraids_geom_null_word_free_cancel_v1
-- name    : TarchaBraids.geom_null_word_free_cancel_v1
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-27T21:04:10.319122+00:00
-- url     : https://prove2.me/theorems/8563ccac-30e1-44e2-95cd-b3a2eec5f1e6
-- title:
--   Free cancellation is invisible to the geometric half-twist lift
-- statement:
--   Diagram-move lemma for Tarcha's Theorem 3.15 (the free, Reidemeister-II-type move among Figures 3.18--3.27): an adjacent cancelling pair FreeGroup.of i * (FreeGroup.of i)^{-1} can be deleted from a word without changing its geometric evaluation, because FreeGroup.lift (halfTwistBraid n) is a group homomorphism. This lets the finite-trace construction of TarchaBraids.geom_null_word_has_contextual_relator_trace_v1 eliminate inverse-pair moves from the diagram analysis.
-- source:
--   Tarcha, Um Estudo Introdutorio da Teoria de Trancas, Theorem 3.15, pp. 59--62, Figures 3.18--3.27; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

/-- Free cancellation does not change the geometric evaluation. -/
theorem geom_null_word_free_cancel_v1 (n : ℕ) (u v : FreeGroup (Fin (n - 1)))
    (i : Fin (n - 1)) :
    FreeGroup.lift (halfTwistBraid n) (u * FreeGroup.of i * (FreeGroup.of i)⁻¹ * v) =
      FreeGroup.lift (halfTwistBraid n) (u * v) := by
  sorry

end TarchaBraids
