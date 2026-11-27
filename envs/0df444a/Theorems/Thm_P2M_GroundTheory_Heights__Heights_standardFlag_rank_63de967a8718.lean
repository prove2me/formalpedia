-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_standardFlag_rank_63de967a8718
-- name    : P2M_GroundTheory_Heights__Heights_standardFlag_rank_63de967a8718
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:09.655477+00:00
-- url     : https://prove2.me/theorems/6e07a115-c96b-4dd8-8319-38024fc7e05d
-- title:
--   P2 M Ground Theory Heights  Heights standard Flag rank 63de967a8718: P2 M Ground Theory Heights  Heights standard Flag rank 63de967a8718
-- statement:
--   The P2 M Ground Theory Heights  Heights standard Flag rank 63de967a8718 construction uses the P2 M Ground Theory Heights  Heights standard Flag rank 63de967a8718 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Slopes.lean#L191-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Slopes.lean#L191-L200

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_standardFlag_rank_63de967a8718 (i : Fin 3) :
    (HermitianBundle.standard K 2).rank (standardFlag K i) = i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«standardFlag_rank» := P2M_GroundTheory_Heights__Heights_standardFlag_rank_63de967a8718
