-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDiv_proof_1d2615c47d14
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDiv_proof_1d2615c47d14
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:36:42.561712+00:00
-- url     : https://prove2.me/theorems/8db6888c-7429-559f-8e4a-d9003809a4df
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Div proof 1d2615c47d14: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Div proof 1d2615c47d14
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Div proof 1d2615c47d14 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Section Div proof 1d2615c47d14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionDiv.lean#L77-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionDiv.lean#L77-L178

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleSectionDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMultAtOfSaturated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTruncSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionDiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleMul_proof_5282581d8898

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
open FlagBundleSectionDivProof

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDiv_proof_1d2615c47d14 (hDim : FlagBundleDim.Statement)
    (hSat : MultAtOfSaturated.Statement.{0}) (hForm : ProjIdealFormValue.Statement)
    (hTrunc : TruncSpecialize.Statement) (hChart : FlagBundleChartSection.Statement) :
    FlagBundleSectionDiv.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleSectionDiv».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDiv_proof_1d2615c47d14
