-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_mem_chartIdeal_iff_bfb81604f357
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_mem_chartIdeal_iff_bfb81604f357
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:52:35.610738+00:00
-- url     : https://prove2.me/theorems/05e54228-5cfb-49ab-a480-b2a6c57dab9b
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim mem chart Ideal iff bfb81604f357: P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim mem chart Ideal iff bfb81604f357
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim mem chart Ideal iff bfb81604f357 construction uses the P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim mem chart Ideal iff bfb81604f357 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartLocDim.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartLocDim.lean#L46-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartLocDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_mem_chartIdeal_iff_bfb81604f357 (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) {p h : MRing ι F} {b : K → ℕ}
    (hp : chartMap Q u p = algebraMap (MRing ι F ⧸ Q) (FractionRing (MRing ι F ⧸ Q))
      (Ideal.Quotient.mk Q h) / algebraMap (MRing ι F ⧸ Q) _ (Ideal.Quotient.mk Q (chartMonomial u b))) :
    p ∈ chartIdeal Q u ↔ h ∈ Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MChartLocDim».«mem_chartIdeal_iff» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_mem_chartIdeal_iff_bfb81604f357
