-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpExcessDecreases_proof_f7630c0bf469
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpExcessDecreases_proof_f7630c0bf469
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:34:22.924748+00:00
-- url     : https://prove2.me/theorems/9e04f115-abcf-51f4-9bef-a4cfee1f6499
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Excess Decreases proof f7630c0bf469: P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Excess Decreases proof f7630c0bf469
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Excess Decreases proof f7630c0bf469 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Excess Decreases proof f7630c0bf469 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ZeroLeDivCycle.lean#L17-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ZeroLeDivCycle.lean#L17-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocalizedQuotientIsSimpleModuleOfMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ZeroLeDivCycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleFiniteSupport_proof_010201f3d63e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53

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
open MvPolynomial
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpExcessDecreases_proof_f7630c0bf469 (hpos : ExcessPositive.Statement.{u})
    (hres : ResidualComparison.Statement.{u}) (hexc : ExceptionalComparison.Statement.{u}) :
    BlowUpExcessDecreases.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BlowUpExcessDecreases».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpExcessDecreases_proof_f7630c0bf469
