-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_liftPairForm_b37bf41d9bb8
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_liftPairForm_b37bf41d9bb8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:35.428984+00:00
-- url     : https://prove2.me/theorems/a3f04617-4fa8-448a-91df-9e242ea7de50
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR rename lift Pair Form b37bf41d9bb8: P2 M Ground Theory Heights  Heights Numbers DVR rename lift Pair Form b37bf41d9bb8
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR rename lift Pair Form b37bf41d9bb8 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR rename lift Pair Form b37bf41d9bb8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L56-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
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
variable (K : Type*)
variable {K} (ι : K → Type) (M M' : ℕ)

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_liftPairForm_b37bf41d9bb8 {R : Type*} [CommRing R] (F : MRing ι R) :
    rename (closureVarEquiv ι M M') (liftPairForm M M' F) = joinForm (ι' := lineBlocks M M') F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«rename_liftPairForm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_liftPairForm_b37bf41d9bb8
