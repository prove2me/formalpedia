-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_isAlgebraic_adjoin_8f5520555759
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_isAlgebraic_adjoin_8f5520555759
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:52:35.862482+00:00
-- url     : https://prove2.me/theorems/91b915aa-7242-4a59-8176-38dbe541be14
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg is Algebraic adjoin 8f5520555759: P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg is Algebraic adjoin 8f5520555759
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg is Algebraic adjoin 8f5520555759 construction uses the P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg is Algebraic adjoin 8f5520555759 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartTrdeg.lean#L142-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartTrdeg.lean#L142-L185

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
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_isAlgebraic_adjoin_8f5520555759 (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    Algebra.IsAlgebraic (Algebra.adjoin (chartMap P u).range (Set.range fun k =>
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, u k⟩))))
      (FractionRing (MRing ι F ⧸ P)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MChartTrdeg».«isAlgebraic_adjoin» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_isAlgebraic_adjoin_8f5520555759
