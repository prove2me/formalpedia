-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMap_monomial_mul_e624b3c488ea
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMap_monomial_mul_e624b3c488ea
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:52:48.655704+00:00
-- url     : https://prove2.me/theorems/6ac6a3bd-648b-4bf3-b83c-6073e68a8302
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers chart Map monomial mul e624b3c488ea: P2 M Ground Theory Heights  Heights Field Numbers chart Map monomial mul e624b3c488ea
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers chart Map monomial mul e624b3c488ea construction uses the P2 M Ground Theory Heights  Heights Field Numbers chart Map monomial mul e624b3c488ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartHomog.lean#L48-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartHomog.lean#L48-L63

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMap_monomial_mul_e624b3c488ea (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) (e : (Σ k, ι k) →₀ ℕ) (c : F) :
    chartMap P u (monomial e c) *
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
          (Ideal.Quotient.mk P (chartMonomial u (Finsupp.weight (blockWeight ι) e))) =
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (monomial e c)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«chartMap_monomial_mul» := P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMap_monomial_mul_e624b3c488ea
