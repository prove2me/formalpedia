-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_vNum_snoc_88f0eb1f0ed1
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_vNum_snoc_88f0eb1f0ed1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:15:53.351637+00:00
-- url     : https://prove2.me/theorems/0539be71-4a10-5138-a276-da6e25094985
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting v Num snoc 88f0eb1f0ed1: P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting v Num snoc 88f0eb1f0ed1
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting v Num snoc 88f0eb1f0ed1 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Vertical Divisors Commuting v Num snoc 88f0eb1f0ed1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WeilNumbersImpVerticalDivisorsCommute.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/WeilNumbersImpVerticalDivisorsCommute.lean#L48-L50

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_vNum_snoc_88f0eb1f0ed1 (W : Ideal (MRing ι O)) {n : ℕ} (L : Fin n → K → ℤ) (b : K → ℤ) :
    vNum W (Fin.snoc (α := fun _ => K → ℤ) L b) = vNum W (Matrix.vecCons b L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«VerticalDivisorsCommuting».«vNum_snoc» := P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommuting_vNum_snoc_88f0eb1f0ed1
