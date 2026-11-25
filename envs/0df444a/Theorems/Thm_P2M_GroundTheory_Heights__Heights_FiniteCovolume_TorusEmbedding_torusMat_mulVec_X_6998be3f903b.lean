-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_X_6998be3f903b
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_X_6998be3f903b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:58:31.126794+00:00
-- url     : https://prove2.me/theorems/54924f64-2367-407c-8d5d-3d6d2133b08c
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding torus Mat mul Vec X 6998be3f903b: P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding torus Mat mul Vec X 6998be3f90
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding torus Mat mul Vec X 6998be3f903b construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding torus Mat mul Vec X 6998be3f903b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusEmbedding.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusEmbedding.lean#L68-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTorusEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.TorusEmbedding
variable {ι : Type*} [Fintype ι]
variable {H : Matrix ι ι ℂ} {X Y : ι → ℂ}
variable [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_X_6998be3f903b (hXX : pair H X X = 0) (hYX : pair H Y X = 1) (s t : ℂ) :
    torusMat H X Y s t *ᵥ X = s • X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«TorusEmbedding».«torusMat_mulVec_X» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_X_6998be3f903b
