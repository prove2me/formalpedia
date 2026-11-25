-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_rename_comp_pointConeMap_7ec05c7ad4fe
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_rename_comp_pointConeMap_7ec05c7ad4fe
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:27:03.852098+00:00
-- url     : https://prove2.me/theorems/0ef5d4e3-0a0f-5b2f-ba50-cb7a37c6a345
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le rename comp point Cone Map 7ec05c7ad4fe: P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le rename comp point Cone Ma
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le rename comp point Cone Map 7ec05c7ad4fe construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Proj Trdeg Le rename comp point Cone Map 7ec05c7ad4fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagProjTrdegLe.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagProjTrdegLe.lean#L26-L33

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_rename_comp_pointConeMap_7ec05c7ad4fe {O Φ : Type} [CommRing O] [Field Φ] [Algebra O Φ] {Λ K' : Type} (ι' : Λ → Type)
    (j : K' ↪ Λ) (pt : (Σ o, ι' o) → Φ) :
    ((rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).restrictScalars O).comp
        (pointConeMap O (fun p => pt (FieldNumbers.blockIncl j ι' p))) =
      (pointConeMap O pt).comp (rename (FieldNumbers.blockIncl j ι')) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagProjTrdegLe».«rename_comp_pointConeMap» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_rename_comp_pointConeMap_7ec05c7ad4fe
