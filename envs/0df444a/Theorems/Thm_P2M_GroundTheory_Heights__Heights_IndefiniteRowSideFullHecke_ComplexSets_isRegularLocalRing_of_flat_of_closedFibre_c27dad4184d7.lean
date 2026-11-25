-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRegularLocalRing_of_flat_of_closedFibre_c27dad4184d7
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRegularLocalRing_of_flat_of_closedFibre_c27dad4184d7
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:20:49.711066+00:00
-- url     : https://prove2.me/theorems/bde91cda-b3ad-4bcb-897b-9d3aee038f9e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Regular Local Ring of flat of closed Fibre c27dad4184d7: P2 M Ground Theory Heights  Heights Indefinite Row Side Full
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Regular Local Ring of flat of closed Fibre c27dad4184d7 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Regular Local Ring of flat of closed Fibre c27dad4184d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSerreRFlatAscentLocal.lean#L30-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSerreRFlatAscentLocal.lean#L30-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSerreRFlatAscentLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRegularLocalRing_of_flat_of_closedFibre_c27dad4184d7 [IsNoetherianRing S] [Module.Flat R S]
    (hR : IsRegularLocalRing R) (hF : IsRegularLocalRing (S ⧸ (maximalIdeal R).map (algebraMap R S))) :
    IsRegularLocalRing S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«isRegularLocalRing_of_flat_of_closedFibre» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRegularLocalRing_of_flat_of_closedFibre_c27dad4184d7
