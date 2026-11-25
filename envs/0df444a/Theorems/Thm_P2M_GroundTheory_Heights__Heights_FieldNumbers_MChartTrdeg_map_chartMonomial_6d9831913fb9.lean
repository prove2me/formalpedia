-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_chartMonomial_6d9831913fb9
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_chartMonomial_6d9831913fb9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:06:04.784728+00:00
-- url     : https://prove2.me/theorems/944821a7-a853-420c-b681-bb61e578c67f
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg map chart Monomial 6d9831913fb9: P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg map chart Monomial 6d9831913fb9
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg map chart Monomial 6d9831913fb9 construction uses the P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg map chart Monomial 6d9831913fb9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartTrdeg.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartTrdeg.lean#L39-L43

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
omit [DecidableEq K] [P.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_chartMonomial_6d9831913fb9 (u : ∀ k, ι k) (b : K → ℕ) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (chartMonomial u b)) =
      ∏ k, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (X ⟨k, u k⟩)) ^ b k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MChartTrdeg».«map_chartMonomial» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_chartMonomial_6d9831913fb9
