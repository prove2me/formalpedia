-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mk_X_chart_705df892b54f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mk_X_chart_705df892b54f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:18.59971+00:00
-- url     : https://prove2.me/theorems/7848a1c2-3cf5-4b4e-9d6a-8ab658c05682
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point mk X chart 705df892b54f: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point mk X chart 705df892b54f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point mk X chart 705df892b54f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point mk X chart 705df892b54f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L37-L40

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mk_X_chart_705df892b54f (i : ∀ k, ι k) (k : K) :
    Ideal.Quotient.mk (chartUnitIdeal (F := F) i) (X ⟨k, i k⟩) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumPoint».«mk_X_chart» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mk_X_chart_705df892b54f
