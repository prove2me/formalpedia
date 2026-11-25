-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finsuppProd_chartVar_6986d97a9298
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_finsuppProd_chartVar_6986d97a9298
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:54:23.051846+00:00
-- url     : https://prove2.me/theorems/af9dad02-4cc9-4a49-ae02-913a6f98d0b9
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers finsupp Prod chart Var 6986d97a9298: P2 M Ground Theory Heights  Heights Field Numbers finsupp Prod chart Var 6986d97a9298
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers finsupp Prod chart Var 6986d97a9298 construction uses the P2 M Ground Theory Heights  Heights Field Numbers finsupp Prod chart Var 6986d97a9298 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartHomog.lean#L31-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartHomog.lean#L31-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartHomog
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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_finsuppProd_chartVar_6986d97a9298 (u : ∀ k, ι k) (e : (Σ k, ι k) →₀ ℕ) :
    (e.prod fun v n => (X ⟨v.1, u v.1⟩ : MRing ι F) ^ n) =
      chartMonomial u (Finsupp.weight (blockWeight ι) e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«finsuppProd_chartVar» := P2M_GroundTheory_Heights__Heights_FieldNumbers_finsuppProd_chartVar_6986d97a9298
