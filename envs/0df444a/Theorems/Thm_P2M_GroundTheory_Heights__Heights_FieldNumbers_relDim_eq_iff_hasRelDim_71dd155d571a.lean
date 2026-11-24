-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_eq_iff_hasRelDim_71dd155d571a
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_eq_iff_hasRelDim_71dd155d571a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:03.972805+00:00
-- url     : https://prove2.me/theorems/5f40418f-c37a-4600-96b6-39d3c01942be
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers rel Dim eq iff has Rel Dim 71dd155d571a: P2 M Ground Theory Heights  Heights Field Numbers rel Dim eq iff has Rel Dim 71dd155d571a
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers rel Dim eq iff has Rel Dim 71dd155d571a construction uses the P2 M Ground Theory Heights  Heights Field Numbers rel Dim eq iff has Rel Dim 71dd155d571a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HomFracDegZeroEqFunField.lean#L14-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/HomFracDegZeroEqFunField.lean#L14-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HomFracDegZeroEqFunField
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
variable {F : Type*} [Field F] {K : Type*} {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_eq_iff_hasRelDim_71dd155d571a [Fintype K] (I : Ideal (MRing ι F)) (n : ℕ) :
    relDim I = (n : WithBot (WithTop ℤ)) ↔ IndefiniteRowSideFullHecke.FieldNumbers.HasRelDim I n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«relDim_eq_iff_hasRelDim» := P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_eq_iff_hasRelDim_71dd155d571a
