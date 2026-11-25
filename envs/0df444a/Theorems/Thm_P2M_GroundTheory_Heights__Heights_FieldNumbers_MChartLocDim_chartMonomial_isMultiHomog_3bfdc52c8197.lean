-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_chartMonomial_isMultiHomog_3bfdc52c8197
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_chartMonomial_isMultiHomog_3bfdc52c8197
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:51:55.718694+00:00
-- url     : https://prove2.me/theorems/23affd97-dff9-502d-bec7-2d9ab168ff03
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim chart Monomial is Multi Homog 3bfdc52c8197: P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim chart Monomial is Multi Ho
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim chart Monomial is Multi Homog 3bfdc52c8197 construction uses the P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim chart Monomial is Multi Homog 3bfdc52c8197 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartLocDim.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartLocDim.lean#L18-L26

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_chartMonomial_isMultiHomog_3bfdc52c8197 (u : ∀ k, ι k) (b : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) u b) b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MChartLocDim».«chartMonomial_isMultiHomog» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_chartMonomial_isMultiHomog_3bfdc52c8197
