-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_mem_colon_span_iff_bab2c8fb31ff
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_mem_colon_span_iff_bab2c8fb31ff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:21.539373+00:00
-- url     : https://prove2.me/theorems/1f652cf2-1b13-5c9d-8430-21646205e6a7
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide mem colon span iff bab2c8fb31ff: P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide mem colon span iff bab2c8fb31ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide mem colon span iff bab2c8fb31ff construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide mem colon span iff bab2c8fb31ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbExactDivide.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbExactDivide.lean#L49-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
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
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_mem_colon_span_iff_bab2c8fb31ff {I : Ideal (MRing ι F)} {s g : MRing ι F} :
    g ∈ I.colon (Ideal.span {s}) ↔ g * s ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbExactDivide».«mem_colon_span_iff» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_mem_colon_span_iff_bab2c8fb31ff
