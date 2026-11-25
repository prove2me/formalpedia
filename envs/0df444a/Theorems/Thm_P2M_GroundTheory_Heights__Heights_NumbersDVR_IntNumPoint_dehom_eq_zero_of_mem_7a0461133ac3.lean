-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_eq_zero_of_mem_7a0461133ac3
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_eq_zero_of_mem_7a0461133ac3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:25.639251+00:00
-- url     : https://prove2.me/theorems/6fdae300-fe43-4146-9e21-de52b6137059
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point dehom eq zero of mem 7a0461133ac3: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point dehom eq zero of mem 7a0461133ac3
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point dehom eq zero of mem 7a0461133ac3 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point dehom eq zero of mem 7a0461133ac3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L140-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L140-L148

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
variable {V}
variable (i : ∀ k, ι k) (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V)
include hi

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_eq_zero_of_mem_7a0461133ac3 (hV : IsMultiHomogIdeal V) {f : MRing ι F} (hf : f ∈ V) :
    dehom V i f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumPoint».«dehom_eq_zero_of_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_eq_zero_of_mem_7a0461133ac3
