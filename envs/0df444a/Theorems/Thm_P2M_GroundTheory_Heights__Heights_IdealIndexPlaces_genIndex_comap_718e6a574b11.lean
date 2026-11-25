-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_genIndex_comap_718e6a574b11
-- name    : P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_genIndex_comap_718e6a574b11
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:20:50.503962+00:00
-- url     : https://prove2.me/theorems/9d554d03-298c-4873-8261-3629a4db0bcd
-- title:
--   P2 M Ground Theory Heights  Heights Ideal Index Places gen Index comap 718e6a574b11: P2 M Ground Theory Heights  Heights Ideal Index Places gen Index comap 718e6a574b11
-- statement:
--   The P2 M Ground Theory Heights  Heights Ideal Index Places gen Index comap 718e6a574b11 construction uses the P2 M Ground Theory Heights  Heights Ideal Index Places gen Index comap 718e6a574b11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PIdealIndexPlaces.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PIdealIndexPlaces.lean#L14-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIdealIndexPlaces
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
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.IdealIndexPlaces

theorem P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_genIndex_comap_718e6a574b11 {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G' →+ G)
    {A B : AddSubgroup G} (hA : A ≤ f.range) (hB : B ≤ f.range) :
    genIndex (A.comap f) (B.comap f) = genIndex A B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IdealIndexPlaces».«genIndex_comap» := P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_genIndex_comap_718e6a574b11
