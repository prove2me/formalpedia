-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_finrank_chart_eq_a442523a379e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_finrank_chart_eq_a442523a379e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:00.256578+00:00
-- url     : https://prove2.me/theorems/2a5333c2-1c4b-522e-b084-ec39b2bac6cb
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point finrank chart eq a442523a379e: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point finrank chart eq a442523a379e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point finrank chart eq a442523a379e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point finrank chart eq a442523a379e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L172-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L172-L217

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_finrank_chart_eq_a442523a379e (V : Ideal (MRing ι F)) (hV : IsMultiProjPrime V) (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V)
    (hfin : haveI := hV.isPrime; FiniteDimensional F (FieldNumbers.homFracDegZero V)) :
    haveI := hV.isPrime
    Module.finrank F (MRing ι F ⧸ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) =
      Module.finrank F (FieldNumbers.homFracDegZero V) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumPoint».«finrank_chart_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_finrank_chart_eq_a442523a379e
