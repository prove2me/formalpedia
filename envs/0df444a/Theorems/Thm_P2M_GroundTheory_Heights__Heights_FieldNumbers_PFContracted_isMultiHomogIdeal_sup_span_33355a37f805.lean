-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomogIdeal_sup_span_33355a37f805
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomogIdeal_sup_span_33355a37f805
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:07.874801+00:00
-- url     : https://prove2.me/theorems/1907a6f7-c4e2-5c37-8309-7eee297462b4
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Multi Homog Ideal sup span 33355a37f805: P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Multi Homog Ideal sup span
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Multi Homog Ideal sup span 33355a37f805 construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted is Multi Homog Ideal sup span 33355a37f805 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L121-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L121-L133

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomogIdeal_sup_span_33355a37f805 {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {f : MRing ι F} {c : K → ℕ} (hf : IsMultiHomog f c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {f}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«isMultiHomogIdeal_sup_span» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomogIdeal_sup_span_33355a37f805
