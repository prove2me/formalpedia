-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_CommonFactorInduction_proof_c80f425604e4
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_CommonFactorInduction_proof_c80f425604e4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:35:09.932804+00:00
-- url     : https://prove2.me/theorems/a6df5ddd-9e6e-539d-a652-1dcac22104e6
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Common Factor Induction proof c80f425604e4: P2 M Ground Theory Heights  Heights Numbers DVR Common Factor Induction proof c80f425604e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Common Factor Induction proof c80f425604e4 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Common Factor Induction proof c80f425604e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Imports.lean#L11-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Imports.lean#L11-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Imports
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_CommonFactorInduction_proof_c80f425604e4 (hpos : ExcessPositive.Statement.{u}) (havoid : AvoidingFormExists.Statement.{u})
    (hhor : HorizontalAvoidingForm.Statement.{u}) (hpieces : BlowUpDecomposition.Statement.{u})
    (hdrop : BlowUpExcessDecreases.Statement.{u}) (hred : BlowUpReduction.Statement.{u})
    (hlhs : LeftSideAdditiveInDegree.Statement.{u}) (hrhs : RightSideMultiplicativeInForm.Statement.{u})
    (hmul : DivCycleMul.Statement.{u}) : CommonFactorInduction.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«CommonFactorInduction».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_CommonFactorInduction_proof_c80f425604e4
