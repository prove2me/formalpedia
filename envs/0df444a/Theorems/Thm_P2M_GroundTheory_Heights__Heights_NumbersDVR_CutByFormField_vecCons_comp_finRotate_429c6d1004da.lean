-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_CutByFormField_vecCons_comp_finRotate_429c6d1004da
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_CutByFormField_vecCons_comp_finRotate_429c6d1004da
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:51.008085+00:00
-- url     : https://prove2.me/theorems/4a075578-08ec-4e68-8f38-e908ce739d37
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Cut By Form Field vec Cons comp fin Rotate 429c6d1004da: P2 M Ground Theory Heights  Heights Numbers DVR Cut By Form Field vec Cons comp fin Rotate 429c
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Cut By Form Field vec Cons comp fin Rotate 429c6d1004da construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Cut By Form Field vec Cons comp fin Rotate 429c6d1004da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PCutByFormField.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PCutByFormField.lean#L18-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByFormField
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
open GroundTheory.Heights₂.Heights.NumbersDVR.CutByFormField

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_CutByFormField_vecCons_comp_finRotate_429c6d1004da {α : Type*} {n : ℕ} (c : α) (bs : Fin n → α) :
    Matrix.vecCons c bs ∘ finRotate (n + 1) = Fin.snoc (α := fun _ => α) bs c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«CutByFormField».«vecCons_comp_finRotate» := P2M_GroundTheory_Heights__Heights_NumbersDVR_CutByFormField_vecCons_comp_finRotate_429c6d1004da
