-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FibreVarieties_proof_00e529182eaf
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FibreVarieties_proof_00e529182eaf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:25.556032+00:00
-- url     : https://prove2.me/theorems/fb164e32-e29c-4f8c-b065-656ef8ca8cf2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Fibre Varieties proof 00e529182eaf: P2 M Ground Theory Heights  Heights Numbers DVR Fibre Varieties proof 00e529182eaf
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Fibre Varieties proof 00e529182eaf construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Fibre Varieties proof 00e529182eaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFibreVarieties.lean#L39-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFibreVarieties.lean#L39-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFibreVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsComponentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFibreVarieties
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FibreVarieties_proof_00e529182eaf
    (hGen : GenericFibProps.Statement.{u}) (hBound : GenericDimBound.Statement.{u})
    (hGe : GenericDimGe.Statement.{u}) (hCorr : SpecialIdealCorresp.Statement.{u})
    (hSpecHomog : SpecialIdealMultiHomog.Statement.{u}) (hSup : SupSpanMultiHomog.Statement.{u})
    (hMin : MinimalPrimeMultiHomog.Statement.{u}) (hQuot : SpecialQuotDim.Statement.{u})
    (hComp : ComponentDim.Statement.{u}) : FibreVarieties.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FibreVarieties».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FibreVarieties_proof_00e529182eaf
