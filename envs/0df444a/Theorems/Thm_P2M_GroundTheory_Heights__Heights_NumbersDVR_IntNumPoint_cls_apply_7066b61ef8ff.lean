-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_cls_apply_7066b61ef8ff
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_cls_apply_7066b61ef8ff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:10.446628+00:00
-- url     : https://prove2.me/theorems/c16126e1-e4de-4c7a-aec5-bd1a49bdec7d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point cls apply 7066b61ef8ff: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point cls apply 7066b61ef8ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point cls apply 7066b61ef8ff construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point cls apply 7066b61ef8ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L86-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
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
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
variable (V : Ideal (MRing ι F)) [V.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_cls_apply_7066b61ef8ff (f : MRing ι F) :
    cls V f = algebraMap (MRing ι F ⧸ V) _ (Ideal.Quotient.mk V f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumPoint».«cls_apply» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_cls_apply_7066b61ef8ff
