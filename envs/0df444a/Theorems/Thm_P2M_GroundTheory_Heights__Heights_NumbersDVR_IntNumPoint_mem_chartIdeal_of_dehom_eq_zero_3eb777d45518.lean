-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mem_chartIdeal_of_dehom_eq_zero_3eb777d45518
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mem_chartIdeal_of_dehom_eq_zero_3eb777d45518
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:23.634609+00:00
-- url     : https://prove2.me/theorems/54bfccd5-1d4e-4344-adf8-26caca6a7d4e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point mem chart Ideal of dehom eq zero 3eb777d45518: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point mem chart Ideal of dehom eq z
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point mem chart Ideal of dehom eq zero 3eb777d45518 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point mem chart Ideal of dehom eq zero 3eb777d45518 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L156-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L156-L168

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mem_chartIdeal_of_dehom_eq_zero_3eb777d45518 {f : MRing ι F} (hf : dehom V i f = 0) :
    f ∈ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumPoint».«mem_chartIdeal_of_dehom_eq_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mem_chartIdeal_of_dehom_eq_zero_3eb777d45518
