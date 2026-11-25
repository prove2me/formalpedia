-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDivProof_divCycle_congr_3f7c8e7470ac
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDivProof_divCycle_congr_3f7c8e7470ac
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:15.944796+00:00
-- url     : https://prove2.me/theorems/09fbc90c-aa74-4782-bf44-89d01048efc4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Div Proof div Cycle congr 3f7c8e7470ac: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Div Proof div Cycle cong
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Div Proof div Cycle congr 3f7c8e7470ac construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Div Proof div Cycle congr 3f7c8e7470ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionDiv.lean#L51-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionDiv.lean#L51-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleSectionDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMultAtOfSaturated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTruncSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionDiv
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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionDivProof

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDivProof_divCycle_congr_3f7c8e7470ac {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {x x' : MRing ι R} (h : x - x' ∈ P) : divCycle P x = divCycle P x' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleSectionDivProof».«divCycle_congr» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDivProof_divCycle_congr_3f7c8e7470ac
