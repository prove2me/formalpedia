-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_imp_cartier_caa24525b62c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_imp_cartier_caa24525b62c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:38.606548+00:00
-- url     : https://prove2.me/theorems/64616d7d-e8ea-4003-ad97-6976880175c0
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting imp cartier caa24525b62c: P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting imp cartier caa24525b6
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting imp cartier caa24525b62c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting imp cartier caa24525b62c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WeilNumbersImpVerticalDivisorsCommute.lean#L115-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WeilNumbersImpVerticalDivisorsCommute.lean#L115-L124

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsComponentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByFormField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivCycleSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WeilNumbersImpVerticalDivisorsCommute
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
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_imp_cartier_caa24525b62c (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) (hDim : ComponentDim.Statement.{u}) :
    VerticalDivisorsCommute.Statement.{u} → VerticalDivisorsCommuting.CartierStatement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«VerticalDivisorsCommuting».«imp_cartier» := P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_imp_cartier_caa24525b62c
