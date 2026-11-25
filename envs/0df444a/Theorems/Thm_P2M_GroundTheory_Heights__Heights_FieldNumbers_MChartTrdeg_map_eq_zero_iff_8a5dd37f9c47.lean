-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_eq_zero_iff_8a5dd37f9c47
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_eq_zero_iff_8a5dd37f9c47
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:35:20.313565+00:00
-- url     : https://prove2.me/theorems/d848ff00-7a99-4926-aff8-c5da43d54394
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg map eq zero iff 8a5dd37f9c47: P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg map eq zero iff 8a5dd37f9c47
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg map eq zero iff 8a5dd37f9c47 construction uses the P2 M Ground Theory Heights  Heights Field Numbers MChart Trdeg map eq zero iff 8a5dd37f9c47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartTrdeg.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartTrdeg.lean#L33-L35

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
omit [Fintype K] [DecidableEq K] [P.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_eq_zero_iff_8a5dd37f9c47 (f : MRing ι F) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) = 0 ↔ f ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MChartTrdeg».«map_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_eq_zero_iff_8a5dd37f9c47
