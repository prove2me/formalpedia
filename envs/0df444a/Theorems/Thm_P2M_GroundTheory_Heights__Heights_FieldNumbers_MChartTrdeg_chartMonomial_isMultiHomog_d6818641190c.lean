-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_chartMonomial_isMultiHomog_d6818641190c
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_chartMonomial_isMultiHomog_d6818641190c
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:52:18.344437+00:00
-- url     : https://prove2.me/theorems/3657233c-008f-4bd3-aea9-07f5f9a5e145
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg chart Monomial is Multi Homog d6818641190c: P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg chart Monomial is Multi Homog
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg chart Monomial is Multi Homog d6818641190c construction uses the P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg chart Monomial is Multi Homog d6818641190c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartTrdeg.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartTrdeg.lean#L18-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartTrdeg
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
open GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_chartMonomial_isMultiHomog_d6818641190c (u : ∀ k, ι k) (b : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) u b) b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MChartTrdeg».«chartMonomial_isMultiHomog» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_chartMonomial_isMultiHomog_d6818641190c
