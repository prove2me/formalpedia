-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_Y_8f10abd9d489
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_Y_8f10abd9d489
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:39.390621+00:00
-- url     : https://prove2.me/theorems/4f88c2c8-9258-493c-96eb-aefc992bfc62
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding torus Mat mul Vec Y 8f10abd9d489: P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding torus Mat mul Vec Y 8f10abd9d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding torus Mat mul Vec Y 8f10abd9d489 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding torus Mat mul Vec Y 8f10abd9d489 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusEmbedding.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusEmbedding.lean#L72-L74

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_Y_8f10abd9d489 (hYY : pair H Y Y = 0) (hXY : pair H X Y = 1) (s t : ℂ) :
    torusMat H X Y s t *ᵥ Y = t • Y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«TorusEmbedding».«torusMat_mulVec_Y» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_Y_8f10abd9d489
