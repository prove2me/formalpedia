-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isHomogeneous_of_isMultiHomogIdeal_b4975a788844
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_isHomogeneous_of_isMultiHomogIdeal_b4975a788844
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:31.166925+00:00
-- url     : https://prove2.me/theorems/adfc395d-f14d-4ba9-89c4-eedc8ea8593f
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers is Homogeneous of is Multi Homog Ideal b4975a788844: P2 M Ground Theory Heights  Heights Field Numbers is Homogeneous of is Multi Homog Ideal b4975a78
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers is Homogeneous of is Multi Homog Ideal b4975a788844 construction uses the P2 M Ground Theory Heights  Heights Field Numbers is Homogeneous of is Multi Homog Ideal b4975a788844 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbDegreeBound.lean#L20-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbDegreeBound.lean#L20-L36

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_isHomogeneous_of_isMultiHomogIdeal_b4975a788844 {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«isHomogeneous_of_isMultiHomogIdeal» := P2M_GroundTheory_Heights__Heights_FieldNumbers_isHomogeneous_of_isMultiHomogIdeal_b4975a788844
