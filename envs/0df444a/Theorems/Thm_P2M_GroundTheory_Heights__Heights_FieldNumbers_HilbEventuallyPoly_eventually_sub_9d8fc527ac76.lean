-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_eventually_sub_9d8fc527ac76
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_eventually_sub_9d8fc527ac76
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:40.132059+00:00
-- url     : https://prove2.me/theorems/f0c04732-d63e-5a44-bbc8-e8192ed2fd18
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly eventually sub 9d8fc527ac76: P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly eventually sub 9d8fc527ac76
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly eventually sub 9d8fc527ac76 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly eventually sub 9d8fc527ac76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HilbEventuallyPolyQualified.lean#L110-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HilbEventuallyPolyQualified.lean#L110-L118

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HilbEventuallyPolyQualified
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
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_eventually_sub_9d8fc527ac76 {P : (K → ℤ) → Prop} (h : ∀ᶠ m in Filter.atTop, P m) (e : K → ℤ) :
    ∀ᶠ m in Filter.atTop, P (m - e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbEventuallyPoly».«eventually_sub» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_eventually_sub_9d8fc527ac76
