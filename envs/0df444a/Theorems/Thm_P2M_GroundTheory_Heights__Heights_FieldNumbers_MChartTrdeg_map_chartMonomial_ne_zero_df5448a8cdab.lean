-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_chartMonomial_ne_zero_df5448a8cdab
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_chartMonomial_ne_zero_df5448a8cdab
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:51:42.452802+00:00
-- url     : https://prove2.me/theorems/5c6a77c2-328a-50e6-afa2-5a730fd644d4
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg map chart Monomial ne zero df5448a8cdab: P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg map chart Monomial ne zero df5448
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg map chart Monomial ne zero df5448a8cdab construction uses the P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg map chart Monomial ne zero df5448a8cdab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartTrdeg.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartTrdeg.lean#L47-L52

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
variable (P : Ideal (MRing ι F)) [P.IsPrime]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_chartMonomial_ne_zero_df5448a8cdab (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P)
    (b : K → ℕ) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P (chartMonomial u b)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MChartTrdeg».«map_chartMonomial_ne_zero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_chartMonomial_ne_zero_df5448a8cdab
