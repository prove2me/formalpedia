-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomogIdeal_sup_span_e78dfa2b1c24
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomogIdeal_sup_span_e78dfa2b1c24
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:30.311299+00:00
-- url     : https://prove2.me/theorems/3ca3ee41-a496-5c1e-a6e9-e0c58ad5bb42
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly is Multi Homog Ideal sup span e78dfa2b1c24: P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly is Multi Homog
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly is Multi Homog Ideal sup span e78dfa2b1c24 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Eventually Poly is Multi Homog Ideal sup span e78dfa2b1c24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HilbEventuallyPolyQualified.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HilbEventuallyPolyQualified.lean#L59-L67

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomogIdeal_sup_span_e78dfa2b1c24 {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s : MRing ι F} {c : K → ℕ} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbEventuallyPoly».«isMultiHomogIdeal_sup_span» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomogIdeal_sup_span_e78dfa2b1c24
