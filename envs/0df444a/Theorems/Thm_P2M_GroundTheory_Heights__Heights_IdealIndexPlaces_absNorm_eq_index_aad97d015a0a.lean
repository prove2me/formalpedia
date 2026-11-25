-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_absNorm_eq_index_aad97d015a0a
-- name    : P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_absNorm_eq_index_aad97d015a0a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:20:18.651904+00:00
-- url     : https://prove2.me/theorems/8f0ded09-b0f3-4b06-ac91-fe7da17a1229
-- title:
--   P2 M Ground Theory Heights  Heights Ideal Index Places abs Norm eq index aad97d015a0a: P2 M Ground Theory Heights  Heights Ideal Index Places abs Norm eq index aad97d015a0a
-- statement:
--   The P2 M Ground Theory Heights  Heights Ideal Index Places abs Norm eq index aad97d015a0a construction uses the P2 M Ground Theory Heights  Heights Ideal Index Places abs Norm eq index aad97d015a0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PIdealIndexPlaces.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PIdealIndexPlaces.lean#L21-L22

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

theorem P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_absNorm_eq_index_aad97d015a0a {L : Type*} [Field L] [NumberField L] (A : Ideal (𝓞 L)) :
    A.absNorm = A.toAddSubgroup.index := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IdealIndexPlaces».«absNorm_eq_index» := P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_absNorm_eq_index_aad97d015a0a
