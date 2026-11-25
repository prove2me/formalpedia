-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_subsingleton_ext_of_flat_d04da1f78642
-- name    : P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_subsingleton_ext_of_flat_d04da1f78642
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:14:59.944196+00:00
-- url     : https://prove2.me/theorems/58af263e-e191-4429-b38d-1378be7f5660
-- title:
--   P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower subsingleton ext of flat d04da1f78642: P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower subsingleton ext of flat
-- statement:
--   The P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower subsingleton ext of flat d04da1f78642 construction uses the P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower subsingleton ext of flat d04da1f78642 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAuslanderBuchsbaumDepthLower.lean#L32-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAuslanderBuchsbaumDepthLower.lean#L32-L48

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

theorem P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_subsingleton_ext_of_flat_d04da1f78642 [IsNoetherianRing R] (rs : List R) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (hrs : IsWeaklyRegular R rs) (P : ModuleCat.{u} R) [Module.Finite R P] [Module.Flat R P] :
    ∀ i < rs.length, Subsingleton (Ext (residueModule R) P i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AuslanderBuchsbaumDepthLower».«subsingleton_ext_of_flat» := P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_subsingleton_ext_of_flat_d04da1f78642
