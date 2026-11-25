-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagProportional_staircase_isHomogeneous_713be1057cf7
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagProportional_staircase_isHomogeneous_713be1057cf7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:19:59.31443+00:00
-- url     : https://prove2.me/theorems/f3b77497-614e-41a3-9571-df5528a6ae8d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Proportional staircase is Homogeneous 713be1057cf7: P2 M Ground Theory Heights  Heights Rest Terms Flag Proportional staircase is Homogeneous 713be1
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Proportional staircase is Homogeneous 713be1057cf7 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Proportional staircase is Homogeneous 713be1057cf7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/StaircaseIsHomogeneous.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/StaircaseIsHomogeneous.lean#L31-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvAtTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvPolynomialReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvMonomialReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStepReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvIdealComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvIdealRepresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStaircaseComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStaircaseDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StaircaseIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagProportional

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagProportional_staircase_isHomogeneous_713be1057cf7 (f j k : ℕ) :
    (monomial (Coinv.staircase f (j + k)) (1 : ℝ)).IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagProportional».«staircase_isHomogeneous» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagProportional_staircase_isHomogeneous_713be1057cf7
