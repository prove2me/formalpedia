-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_map_e1ed5f7bf88c
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_map_e1ed5f7bf88c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:33.220568+00:00
-- url     : https://prove2.me/theorems/a5606639-d461-4f8b-9a4c-f7edfbb27615
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog Ideal map e1ed5f7bf88c: P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog Ideal map e1ed5f7bf88c
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog Ideal map e1ed5f7bf88c construction uses the P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog Ideal map e1ed5f7bf88c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L135-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L135-L141

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
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
variable {σ : Type*} {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
variable {K : Type*} {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_map_e1ed5f7bf88c [DecidableEq K] {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    IsMultiHomogIdeal (I.map (map (algebraMap F F'))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«isMultiHomogIdeal_map» := P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_map_e1ed5f7bf88c
