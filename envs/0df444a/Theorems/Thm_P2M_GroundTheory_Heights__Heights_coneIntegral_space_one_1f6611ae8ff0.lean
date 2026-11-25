-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneIntegral_space_one_1f6611ae8ff0
-- name    : P2M_GroundTheory_Heights__Heights_coneIntegral_space_one_1f6611ae8ff0
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:02.949199+00:00
-- url     : https://prove2.me/theorems/41c612b4-a832-4348-ad19-994667d82d28
-- title:
--   P2 M Ground Theory Heights  Heights cone Integral space one 1f6611ae8ff0: P2 M Ground Theory Heights  Heights cone Integral space one 1f6611ae8ff0
-- statement:
--   The P2 M Ground Theory Heights  Heights cone Integral space one 1f6611ae8ff0 construction uses the P2 M Ground Theory Heights  Heights cone Integral space one 1f6611ae8ff0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeToProjective.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeToProjective.lean#L14-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConePolar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaneSliceMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeToProjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_coneIntegral_space_one_1f6611ae8ff0 (e : ℕ) :
    coneIntegral (HermNorm.std (e + 1)) (⊥ : Ideal (MvPolynomial (Fin (e + 1)) ℂ)) e
      (fun _ => 1) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coneIntegral_space_one» := P2M_GroundTheory_Heights__Heights_coneIntegral_space_one_1f6611ae8ff0
