-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_blocks_le_1e793719e155
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_blocks_le_1e793719e155
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:10.841176+00:00
-- url     : https://prove2.me/theorems/8ac42bc5-d290-4257-8c4a-3b6cb01c0abf
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg blocks le 1e793719e155: P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg blocks le 1e793719e155
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg blocks le 1e793719e155 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le trdeg blocks le 1e793719e155 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagProjTrdegLe.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagProjTrdegLe.lean#L35-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagProjSpecialDimSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PAdjoinTrdegAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagProjTrdegLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_blocks_le_1e793719e155 {O Φ : Type} [CommRing O] [Field Φ] [Algebra O Φ] {Λ K' : Type} (ι' : Λ → Type)
    (j : K' ↪ Λ) (pt : (Σ o, ι' o) → Φ) :
    Algebra.trdeg O (MvPolynomial (Σ o, ι' (j o)) O ⧸ pointIdeal O (fun p => pt (FieldNumbers.blockIncl j ι' p))) ≤
      Algebra.trdeg O (MvPolynomial (Σ o, ι' o) O ⧸ pointIdeal O pt) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagProjTrdegLe».«trdeg_blocks_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_blocks_le_1e793719e155
