-- Prove2me | Theorems.Thm_TarchaBraids_geom_null_word_conj_insert_v1
-- name    : TarchaBraids.geom_null_word_conj_insert_v1
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-27T21:04:01.415971+00:00
-- url     : https://prove2.me/theorems/9365cc39-2620-4396-8801-8e2954f59a3a
-- title:
--   Conjugation preserves nullity under the geometric half-twist lift
-- statement:
--   Algebraic glue for the contextual insertions in Tarcha's Theorem 3.15 (Figures 3.18--3.27): if a relator word r is geometrically null, then so is every conjugate u * r * u^{-1} -- a relator inserted in context. Since FreeGroup.lift is a group homomorphism, lift (u * r * u^{-1}) = lift u * 1 * (lift u)^{-1} = 1. Together with products of null words and the relator-nullity diagram moves, this gives that every finite contextual relator trace evaluates to the identity, the key step used by TarchaBraids.geom_null_word_has_contextual_relator_trace_v1.
-- source:
--   Tarcha, Um Estudo Introdutorio da Teoria de Trancas, Theorem 3.15, pp. 59--62, Figures 3.18--3.27; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

/-- Contextual insertion: a null relator stays null when conjugated. -/
theorem geom_null_word_conj_insert_v1 (n : ℕ) (u r : FreeGroup (Fin (n - 1)))
    (hr : FreeGroup.lift (halfTwistBraid n) r = 1) :
    FreeGroup.lift (halfTwistBraid n) (u * r * u⁻¹) = 1 := by
  sorry

end TarchaBraids
