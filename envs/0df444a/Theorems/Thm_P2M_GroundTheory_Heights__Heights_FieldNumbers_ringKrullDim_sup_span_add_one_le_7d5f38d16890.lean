-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ringKrullDim_sup_span_add_one_le_7d5f38d16890
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ringKrullDim_sup_span_add_one_le_7d5f38d16890
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:45.364142+00:00
-- url     : https://prove2.me/theorems/bf303311-152b-45d3-8c19-ab638ed699ff
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers ring Krull Dim sup span add one le 7d5f38d16890: P2 M Ground Theory Heights  Heights Field Numbers ring Krull Dim sup span add one le 7d5f38d16890
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers ring Krull Dim sup span add one le 7d5f38d16890 construction uses the P2 M Ground Theory Heights  Heights Field Numbers ring Krull Dim sup span add one le 7d5f38d16890 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbDegreeBound.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbDegreeBound.lean#L58-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbDegreeBound
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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ringKrullDim_sup_span_add_one_le_7d5f38d16890 {P : Ideal (MRing ι F)} [P.IsPrime] {s : MRing ι F}
    (hs : s ∉ P) :
    ringKrullDim (MRing ι F ⧸ (P ⊔ Ideal.span {s})) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ringKrullDim_sup_span_add_one_le» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ringKrullDim_sup_span_add_one_le_7d5f38d16890
