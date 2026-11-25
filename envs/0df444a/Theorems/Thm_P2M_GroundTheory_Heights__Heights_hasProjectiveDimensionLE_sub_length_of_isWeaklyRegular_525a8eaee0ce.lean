-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular_525a8eaee0ce
-- name    : P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular_525a8eaee0ce
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:53.942502+00:00
-- url     : https://prove2.me/theorems/b2d809c2-1ec1-44e9-953b-67d5bcfabfbe
-- title:
--   P2 M Ground Theory Heights  Heights has Projective Dimension LE sub length of is Weakly Regular 525a8eaee0ce: P2 M Ground Theory Heights  Heights has Projective Dimension LE sub length of is Weakly Re
-- statement:
--   The P2 M Ground Theory Heights  Heights has Projective Dimension LE sub length of is Weakly Regular 525a8eaee0ce construction uses the P2 M Ground Theory Heights  Heights has Projective Dimension LE sub length of is Weakly Regular 525a8eaee0ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAuslanderBuchsbaumProjDimUpper.lean#L12-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAuslanderBuchsbaumProjDimUpper.lean#L12-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumProjDimUpper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AuslanderBuchsbaumDepthBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAuslanderBuchsbaumProjDimUpper
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
open IsLocalRing CategoryTheory RingTheory.Sequence
universe u

theorem P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular_525a8eaee0ce (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (d : ℕ)
    (hd : ∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d)
    (ms : List R) : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] (n : ℕ),
      HasProjectiveDimensionLE (ModuleCat.of R M) n → (∀ r ∈ ms, r ∈ maximalIdeal R) →
        IsWeaklyRegular M ms → HasProjectiveDimensionLE (ModuleCat.of R M) (d - ms.length) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular» := P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular_525a8eaee0ce
