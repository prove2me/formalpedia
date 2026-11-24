-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_redEval_divO_27c775010d0b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_redEval_divO_27c775010d0b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:38:17.025545+00:00
-- url     : https://prove2.me/theorems/0bdf4d6c-3c78-466a-aa58-c027f3a78493
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting red Eval div O 27c775010d0b: P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting red Eval div O 27c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting red Eval div O 27c775010d0b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting red Eval div O 27c775010d0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WeilNumbersImpVerticalDivisorsCommute.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WeilNumbersImpVerticalDivisorsCommute.lean#L52-L59

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
open GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorsCommuting
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_redEval_divO_27c775010d0b (J : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ)
    (P : Ideal (MRing ι O)) (f g : MRing ι O) :
    IndefiniteRowSideFullHecke.NumbersDVR.redEval J (IndefiniteRowSideFullHecke.NumbersDVR.divO P f g) =
      cycEval (fun W => J (specialIdeal W)) (ratDiv P f g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«VerticalDivisorsCommuting».«redEval_divO» := P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_redEval_divO_27c775010d0b
