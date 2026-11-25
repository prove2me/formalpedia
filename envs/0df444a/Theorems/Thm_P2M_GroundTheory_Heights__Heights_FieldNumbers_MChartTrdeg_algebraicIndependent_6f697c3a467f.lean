-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_algebraicIndependent_6f697c3a467f
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_algebraicIndependent_6f697c3a467f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:51:36.109156+00:00
-- url     : https://prove2.me/theorems/de0915fc-f68c-5d94-81fb-2951ad4f17ff
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg algebraic Independent 6f697c3a467f: P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg algebraic Independent 6f697c3a467f
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg algebraic Independent 6f697c3a467f construction uses the P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg algebraic Independent 6f697c3a467f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartTrdeg.lean#L54-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartTrdeg.lean#L54-L138

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_algebraicIndependent_6f697c3a467f (hH : MChartHomog.Statement.{u}) (hP : IsMultiHomogIdeal P)
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    AlgebraicIndependent (chartMap P u).range (fun k => algebraMap (MRing ι F ⧸ P)
      (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, u k⟩))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MChartTrdeg».«algebraicIndependent» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_algebraicIndependent_6f697c3a467f
