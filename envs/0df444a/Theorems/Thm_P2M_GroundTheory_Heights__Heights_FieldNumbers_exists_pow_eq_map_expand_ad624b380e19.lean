-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_pow_eq_map_expand_ad624b380e19
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_pow_eq_map_expand_ad624b380e19
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:53.565215+00:00
-- url     : https://prove2.me/theorems/710ff125-1a8a-5ee0-a771-289b8521370c
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers exists pow eq map expand ad624b380e19: P2 M Ground Theory Heights  Heights Field Numbers exists pow eq map expand ad624b380e19
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers exists pow eq map expand ad624b380e19 construction uses the P2 M Ground Theory Heights  Heights Field Numbers exists pow eq map expand ad624b380e19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherCharPLemmas.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherCharPLemmas.lean#L8-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherCharPLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open Polynomial

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_pow_eq_map_expand_ad624b380e19 {σ k k' : Type*} [Field k] [Field k'] [Algebra k k'] (p : ℕ)
    [Fact p.Prime] [CharP k' p] (e : ℕ) (N : MvPolynomial σ k)
    (hN : ∀ m, ∃ z : k', z ^ p ^ e = algebraMap k k' (N.coeff m)) :
    ∃ N' : MvPolynomial σ k',
      N' ^ p ^ e = MvPolynomial.map (algebraMap k k') (MvPolynomial.expand (p ^ e) N) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«exists_pow_eq_map_expand» := P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_pow_eq_map_expand_ad624b380e19
