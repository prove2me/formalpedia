-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_chartMonomial_not_mem_42e86f0424ae
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_chartMonomial_not_mem_42e86f0424ae
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:38:37.166279+00:00
-- url     : https://prove2.me/theorems/ee936d31-7e73-44f1-aa54-1e179411b5c8
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim chart Monomial not mem 42e86f0424ae: P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim chart Monomial not mem 42e86f0424
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim chart Monomial not mem 42e86f0424ae construction uses the P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim chart Monomial not mem 42e86f0424ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartLocDim.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartLocDim.lean#L30-L35

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_chartMonomial_not_mem_42e86f0424ae (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) (b : K → ℕ) : chartMonomial u b ∉ Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MChartLocDim».«chartMonomial_not_mem» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_chartMonomial_not_mem_42e86f0424ae
