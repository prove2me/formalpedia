-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_mapExpand_723755a99971
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_mapExpand_723755a99971
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:19.298342+00:00
-- url     : https://prove2.me/theorems/b348c63d-07f1-4e95-a382-644c97e86b9c
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers finite map Expand 723755a99971: P2 M Ground Theory Heights  Heights Field Numbers finite map Expand 723755a99971
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers finite map Expand 723755a99971 construction uses the P2 M Ground Theory Heights  Heights Field Numbers finite map Expand 723755a99971 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherCharPLemmas.lean#L20-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/NoetherCharPLemmas.lean#L20-L52

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_mapExpand_723755a99971 (k k' : Type*) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] (σ : Type*) [Finite σ] (q : ℕ) (hq : 0 < q) :
    ((MvPolynomial.mapAlgHom (σ := σ) (Algebra.ofId k k')).comp
      (MvPolynomial.expand q)).toRingHom.Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«finite_mapExpand» := P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_mapExpand_723755a99971
