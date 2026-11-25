-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_subsingleton_ext_of_hasProjectiveDimensionLE_3df477c9653d
-- name    : P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_subsingleton_ext_of_hasProjectiveDimensionLE_3df477c9653d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:20.636194+00:00
-- url     : https://prove2.me/theorems/b2420455-6b6c-420b-ad93-cf1cd2da6426
-- title:
--   P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower subsingleton ext of has Projective Dimension LE 3df477c9653d: P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower su
-- statement:
--   The P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower subsingleton ext of has Projective Dimension LE 3df477c9653d construction uses the P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower subsingleton ext of has Projective Dimension LE 3df477c9653d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAuslanderBuchsbaumDepthLower.lean#L50-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAuslanderBuchsbaumDepthLower.lean#L50-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAuslanderBuchsbaumDepthLower
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
open IsLocalRing CategoryTheory Limits Abelian RingTheory.Sequence
universe u
open GroundTheory.Heights₂.Heights.AuslanderBuchsbaumDepthLower
variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_subsingleton_ext_of_hasProjectiveDimensionLE_3df477c9653d [IsNoetherianRing R] (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R) (hrs : IsWeaklyRegular R rs) (ℓ : ℕ) :
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M], HasProjectiveDimensionLE M ℓ →
      ∀ i, i + ℓ < rs.length → Subsingleton (Ext (residueModule R) M i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AuslanderBuchsbaumDepthLower».«subsingleton_ext_of_hasProjectiveDimensionLE» := P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_subsingleton_ext_of_hasProjectiveDimensionLE_3df477c9653d
