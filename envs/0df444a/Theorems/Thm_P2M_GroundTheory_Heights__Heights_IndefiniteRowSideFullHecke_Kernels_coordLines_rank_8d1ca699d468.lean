-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_rank_8d1ca699d468
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_rank_8d1ca699d468
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:01.309389+00:00
-- url     : https://prove2.me/theorems/b67dbd93-eda4-416a-9190-88671eeb3819
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels coord Lines rank 8d1ca699d468: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels coord Lines rank 8d
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels coord Lines rank 8d1ca699d468 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels coord Lines rank 8d1ca699d468 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardInnerSingleNe.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardInnerSingleNe.lean#L38-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField TensorProduct GroundTheory.Heights₂.Heights
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_rank_8d1ca699d468 (K : Type*) [Field K] [NumberField K] (x : Fin 2) :
    (HermitianBundle.standard K 2).rank (coordLines K x) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«coordLines_rank» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_rank_8d1ca699d468
