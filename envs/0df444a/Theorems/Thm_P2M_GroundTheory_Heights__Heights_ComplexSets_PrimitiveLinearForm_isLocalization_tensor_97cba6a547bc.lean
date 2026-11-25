-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_isLocalization_tensor_97cba6a547bc
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_isLocalization_tensor_97cba6a547bc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:01.867403+00:00
-- url     : https://prove2.me/theorems/02bb6660-b5b6-5d41-aec7-722e9b8b45e3
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Primitive Linear Form is Localization tensor 97cba6a547bc: P2 M Ground Theory Heights  Heights Complex Sets Primitive Linear Form is Localization tenso
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Primitive Linear Form is Localization tensor 97cba6a547bc construction uses the P2 M Ground Theory Heights  Heights Complex Sets Primitive Linear Form is Localization tensor 97cba6a547bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PrimitiveLinearForm.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PrimitiveLinearForm.lean#L18-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PrimitiveLinearForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open Polynomial TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveLinearForm
variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
attribute [local instance] tensorRightAlgebra

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_isLocalization_tensor_97cba6a547bc :
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (FractionRing R ⊗[R] B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«PrimitiveLinearForm».«isLocalization_tensor» := P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_isLocalization_tensor_97cba6a547bc
