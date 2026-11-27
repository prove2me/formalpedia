-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpReduction_proof_fb534c2b504e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpReduction_proof_fb534c2b504e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:38:04.465207+00:00
-- url     : https://prove2.me/theorems/c3b31245-5b1a-404e-a6fb-dcdfcd8bee4c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Reduction proof fb534c2b504e: P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Reduction proof fb534c2b504e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Reduction proof fb534c2b504e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Reduction proof fb534c2b504e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ExceptionalDeg.lean#L11-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ExceptionalDeg.lean#L11-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ExceptionalDeg
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpReduction_proof_fb534c2b504e (hpieces : BlowUpDecomposition.Statement.{u})
    (hinv : BlowUpInvariance.Statement.{u}) (hcf : CommonFactorRemoval.Statement.{u})
    (hadd : AdditivityInDivisor.Statement.{u}) (hrhs : RightSideMultiplicativeInForm.Statement.{u})
    (hlhs : LeftSideAdditiveInDegree.Statement.{u}) (htaut : TautologicalCase.Statement.{u}) :
    BlowUpReduction.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BlowUpReduction».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpReduction_proof_fb534c2b504e
