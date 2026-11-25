-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_hilbFn_map_ba3c10076c2a
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_hilbFn_map_ba3c10076c2a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:00.635798+00:00
-- url     : https://prove2.me/theorems/b62f052c-1c4e-5ef3-8870-cb9824f27824
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers hilb Fn map ba3c10076c2a: P2 M Ground Theory Heights  Heights Field Numbers hilb Fn map ba3c10076c2a
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers hilb Fn map ba3c10076c2a construction uses the P2 M Ground Theory Heights  Heights Field Numbers hilb Fn map ba3c10076c2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L260-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L260-L265

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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_hilbFn_map_ba3c10076c2a (I : Ideal (MRing ι F)) (m : K → ℤ) :
    hilbFn (I.map (map (algebraMap F F'))) m = hilbFn I m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«hilbFn_map» := P2M_GroundTheory_Heights__Heights_FieldNumbers_hilbFn_map_ba3c10076c2a
