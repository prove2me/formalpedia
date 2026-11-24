-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_cls_eq_zero_iff_7938877721c2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_cls_eq_zero_iff_7938877721c2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:28.381602+00:00
-- url     : https://prove2.me/theorems/5c0c9215-8364-49ef-9cb6-4e3bb42d8c54
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point cls eq zero iff 7938877721c2: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point cls eq zero iff 7938877721c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point cls eq zero iff 7938877721c2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point cls eq zero iff 7938877721c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L89-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L89-L90

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_cls_eq_zero_iff_7938877721c2 (f : MRing ι F) : cls V f = 0 ↔ f ∈ V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumPoint».«cls_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_cls_eq_zero_iff_7938877721c2
