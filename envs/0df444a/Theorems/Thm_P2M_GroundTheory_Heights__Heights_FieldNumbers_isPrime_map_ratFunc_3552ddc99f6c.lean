-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isPrime_map_ratFunc_3552ddc99f6c
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_isPrime_map_ratFunc_3552ddc99f6c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:36.600579+00:00
-- url     : https://prove2.me/theorems/021c88cf-2396-485a-9e35-cb9a65645177
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers is Prime map rat Func 3552ddc99f6c: P2 M Ground Theory Heights  Heights Field Numbers is Prime map rat Func 3552ddc99f6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers is Prime map rat Func 3552ddc99f6c construction uses the P2 M Ground Theory Heights  Heights Field Numbers is Prime map rat Func 3552ddc99f6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L293-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L293-L316

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
variable {σ : Type*} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_isPrime_map_ratFunc_3552ddc99f6c (P : Ideal (MvPolynomial σ F)) [hP : P.IsPrime] :
    (P.map (map (algebraMap F (RatFunc F)) : MvPolynomial σ F →+* _)).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«isPrime_map_ratFunc» := P2M_GroundTheory_Heights__Heights_FieldNumbers_isPrime_map_ratFunc_3552ddc99f6c
