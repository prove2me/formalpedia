-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le_7f33b2b57839
-- name    : P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le_7f33b2b57839
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:54.563203+00:00
-- url     : https://prove2.me/theorems/312b5a65-da35-49f9-8ced-bfab0a4ea357
-- title:
--   P2 M Ground Theory Heights  Heights has Projective Dimension LE of forall is Weakly Regular length le 7f33b2b57839: P2 M Ground Theory Heights  Heights has Projective Dimension LE of forall is Weakly
-- statement:
--   The P2 M Ground Theory Heights  Heights has Projective Dimension LE of forall is Weakly Regular length le 7f33b2b57839 construction uses the P2 M Ground Theory Heights  Heights has Projective Dimension LE of forall is Weakly Regular length le 7f33b2b57839 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/AuslanderBuchsbaumDepthBound.lean#L140-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/AuslanderBuchsbaumDepthBound.lean#L140-L183

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

theorem P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le_7f33b2b57839 (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      (∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d) →
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ),
        HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1) →
          HasProjectiveDimensionLE (ModuleCat.of R M) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le» := P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le_7f33b2b57839
