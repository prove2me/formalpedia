-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimensionInequality_tower_step_cfa42bc38561
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_DimensionInequality_tower_step_cfa42bc38561
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:20.478163+00:00
-- url     : https://prove2.me/theorems/83f00474-ea56-5a17-8388-c7219b48597f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Dimension Inequality tower step cfa42bc38561: P2 M Ground Theory Heights  Heights Numbers DVR Dimension Inequality tower step cfa42bc38561
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Dimension Inequality tower step cfa42bc38561 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Dimension Inequality tower step cfa42bc38561 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDimensionInequality.lean#L12-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDimensionInequality.lean#L12-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDimensionInequality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDimensionInequalitySteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimensionInequality
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
universe u v
open Cardinal

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_DimensionInequality_tower_step_cfa42bc38561 {A : Type u} {C B : Type v} [CommRing A] [CommRing C]
    [CommRing B] [IsDomain A] [IsDomain C] [IsDomain B] [Algebra A C] [Algebra C B] [Algebra A B]
    [IsScalarTower A C B] (hAC : Function.Injective (algebraMap A C))
    (hCB : Function.Injective (algebraMap C B)) (P : Ideal B) [P.IsPrime] (Q : Ideal C) [Q.IsPrime]
    (p : Ideal A) [p.IsPrime] [P.LiesOver Q] [Q.LiesOver p] [P.LiesOver p]
    (e₁ : ofENat Q.height + Algebra.trdeg (A ⧸ p) (C ⧸ Q) ≤ ofENat p.height + Algebra.trdeg A C)
    (e₂ : ofENat P.height + Algebra.trdeg (C ⧸ Q) (B ⧸ P) ≤ ofENat Q.height + Algebra.trdeg C B) :
    ofENat P.height + Algebra.trdeg (A ⧸ p) (B ⧸ P) ≤ ofENat p.height + Algebra.trdeg A B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«DimensionInequality».«tower_step» := P2M_GroundTheory_Heights__Heights_NumbersDVR_DimensionInequality_tower_step_cfa42bc38561
