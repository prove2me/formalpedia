-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_orth_2b820cb671e4
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_orth_2b820cb671e4
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:10.61295+00:00
-- url     : https://prove2.me/theorems/45b094a3-c055-5f97-aa44-53cf1173c08d
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding torus Mat mul Vec orth 2b820cb671e4: P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding torus Mat mul Vec orth 2b82
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding torus Mat mul Vec orth 2b820cb671e4 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Torus Embedding torus Mat mul Vec orth 2b820cb671e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusEmbedding.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusEmbedding.lean#L76-L78

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_orth_2b820cb671e4 (s t : ℂ) (z : ι → ℂ) (hX : pair H X z = 0) (hY : pair H Y z = 0) :
    torusMat H X Y s t *ᵥ z = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«TorusEmbedding».«torusMat_mulVec_orth» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusEmbedding_torusMat_mulVec_orth_2b820cb671e4
