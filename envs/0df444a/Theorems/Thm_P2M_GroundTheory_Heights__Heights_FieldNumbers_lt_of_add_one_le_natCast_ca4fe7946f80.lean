-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_lt_of_add_one_le_natCast_ca4fe7946f80
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_lt_of_add_one_le_natCast_ca4fe7946f80
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:21.602916+00:00
-- url     : https://prove2.me/theorems/5d1df0f2-f659-4ca2-b38b-4bc97f2a2542
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers lt of add one le nat Cast ca4fe7946f80: P2 M Ground Theory Heights  Heights Field Numbers lt of add one le nat Cast ca4fe7946f80
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers lt of add one le nat Cast ca4fe7946f80 construction uses the P2 M Ground Theory Heights  Heights Field Numbers lt of add one le nat Cast ca4fe7946f80 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbDegreeBound.lean#L67-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbDegreeBound.lean#L67-L80

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_lt_of_add_one_le_natCast_ca4fe7946f80 {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ n) : x < n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«lt_of_add_one_le_natCast» := P2M_GroundTheory_Heights__Heights_FieldNumbers_lt_of_add_one_le_natCast_ca4fe7946f80
