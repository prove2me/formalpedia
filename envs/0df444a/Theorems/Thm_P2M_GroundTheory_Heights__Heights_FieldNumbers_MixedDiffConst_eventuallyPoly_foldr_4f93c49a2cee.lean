-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eventuallyPoly_foldr_4f93c49a2cee
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eventuallyPoly_foldr_4f93c49a2cee
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:02.105312+00:00
-- url     : https://prove2.me/theorems/8da8b8d5-f9d4-5a42-a35b-195219730532
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const eventually Poly foldr 4f93c49a2cee: P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const eventually Poly foldr 4f93c49a
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const eventually Poly foldr 4f93c49a2cee construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mixed Diff Const eventually Poly foldr 4f93c49a2cee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMixedDiffConst.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMixedDiffConst.lean#L100-L104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMixedDiffConst
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
variable {K : Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eventuallyPoly_foldr_4f93c49a2cee (L : List (K → ℤ)) {h : (K → ℤ) → ℤ} {p : MvPolynomial K ℚ}
    (hp : EventuallyPoly h p) : EventuallyPoly (L.foldr diffStep h) (L.foldr polyStep p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MixedDiffConst».«eventuallyPoly_foldr» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eventuallyPoly_foldr_4f93c49a2cee
