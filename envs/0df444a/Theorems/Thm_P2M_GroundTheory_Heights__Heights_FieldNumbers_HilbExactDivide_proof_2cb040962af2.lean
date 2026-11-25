-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_proof_2cb040962af2
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_proof_2cb040962af2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:29.306805+00:00
-- url     : https://prove2.me/theorems/76efd358-7f8b-5063-aa05-2fd58e54ecd0
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide proof 2cb040962af2: P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide proof 2cb040962af2
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide proof 2cb040962af2 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide proof 2cb040962af2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbExactDivide.lean#L152-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbExactDivide.lean#L152-L190

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_GradedFinite_proof_4a0254b94345

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_proof_2cb040962af2 (h1 : GradedFinite.Statement.{u}) : HilbExactDivide.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbExactDivide».«proof» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_proof_2cb040962af2
