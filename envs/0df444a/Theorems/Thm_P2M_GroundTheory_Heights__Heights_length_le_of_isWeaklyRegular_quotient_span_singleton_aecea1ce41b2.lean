-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_le_of_isWeaklyRegular_quotient_span_singleton_aecea1ce41b2
-- name    : P2M_GroundTheory_Heights__Heights_length_le_of_isWeaklyRegular_quotient_span_singleton_aecea1ce41b2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:52.955888+00:00
-- url     : https://prove2.me/theorems/4a8ec903-e245-4aad-9649-82e6bd79ea91
-- title:
--   P2 M Ground Theory Heights  Heights length le of is Weakly Regular quotient span singleton aecea1ce41b2: P2 M Ground Theory Heights  Heights length le of is Weakly Regular quotient span singleton aece
-- statement:
--   The P2 M Ground Theory Heights  Heights length le of is Weakly Regular quotient span singleton aecea1ce41b2 construction uses the P2 M Ground Theory Heights  Heights length le of is Weakly Regular quotient span singleton aecea1ce41b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/AuslanderBuchsbaumDepthBound.lean#L105-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/AuslanderBuchsbaumDepthBound.lean#L105-L138

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AuslanderBuchsbaumDepthBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing CategoryTheory RingTheory.Sequence Ideal
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_length_le_of_isWeaklyRegular_quotient_span_singleton_aecea1ce41b2 [IsLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) [IsLocalRing (R ⧸ span {x})] (d : ℕ)
    (hd : ∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d + 1)
    (rs : List (R ⧸ span {x})) (hrs : ∀ r ∈ rs, r ∈ maximalIdeal (R ⧸ span {x}))
    (hreg : IsWeaklyRegular (R ⧸ span {x}) rs) : rs.length ≤ d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«length_le_of_isWeaklyRegular_quotient_span_singleton» := P2M_GroundTheory_Heights__Heights_length_le_of_isWeaklyRegular_quotient_span_singleton_aecea1ce41b2
