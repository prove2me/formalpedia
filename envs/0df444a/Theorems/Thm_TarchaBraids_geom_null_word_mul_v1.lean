-- Prove2me | Theorems.Thm_TarchaBraids_geom_null_word_mul_v1
-- name    : TarchaBraids.geom_null_word_mul_v1
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-27T21:03:55.777909+00:00
-- url     : https://prove2.me/theorems/005f326f-bba8-4bbb-9908-da94d4c2bac0
-- title:
--   Products of null words are null under the geometric half-twist lift
-- statement:
--   Algebraic glue for the finite trace in Tarcha's Theorem 3.15 (Figures 3.18--3.27): FreeGroup.lift (halfTwistBraid n) is a group homomorphism, so the product of two geometrically-null words is geometrically null. A finite contextual relator trace is such a product (of conjugated Artin relators), hence evaluates to the identity; this lemma is the induction step assembling the trace in TarchaBraids.geom_null_word_has_contextual_relator_trace_v1.
-- source:
--   Tarcha, Um Estudo Introdutorio da Teoria de Trancas, Theorem 3.15, pp. 59--62, Figures 3.18--3.27; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

/-- The trace assembly step: products of null words stay null. -/
theorem geom_null_word_mul_v1 (n : ℕ) (w₁ w₂ : FreeGroup (Fin (n - 1)))
    (h₁ : FreeGroup.lift (halfTwistBraid n) w₁ = 1)
    (h₂ : FreeGroup.lift (halfTwistBraid n) w₂ = 1) :
    FreeGroup.lift (halfTwistBraid n) (w₁ * w₂) = 1 := by
  sorry

end TarchaBraids
