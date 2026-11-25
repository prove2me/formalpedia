-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_equiv_7cca2fd178c2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_equiv_7cca2fd178c2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:10:20.151958+00:00
-- url     : https://prove2.me/theorems/5c7ef13b-e0dc-4a3c-8a86-ea7ffdea60a5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting equiv 7cca2fd178c2: P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting equiv 7cca2fd178c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting equiv 7cca2fd178c2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting equiv 7cca2fd178c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WeilNumbersImpVerticalDivisorsCommute.lean#L126-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WeilNumbersImpVerticalDivisorsCommute.lean#L126-L129

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_equiv_f121b6417e76

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_equiv_7cca2fd178c2 (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) (hDim : ComponentDim.Statement.{u}) :
    VerticalDivisorsCommute.Statement.{u} ↔ VerticalDivisorsCommuting.CartierStatement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«VerticalDivisorsCommuting».«equiv» := P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_equiv_7cca2fd178c2
