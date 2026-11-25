-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isPrime_map_polynomial_6eef1ef7fe50
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_isPrime_map_polynomial_6eef1ef7fe50
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:28.165894+00:00
-- url     : https://prove2.me/theorems/2b607589-0d92-4ef6-a629-3737c18aab54
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers is Prime map polynomial 6eef1ef7fe50: P2 M Ground Theory Heights  Heights Field Numbers is Prime map polynomial 6eef1ef7fe50
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers is Prime map polynomial 6eef1ef7fe50 construction uses the P2 M Ground Theory Heights  Heights Field Numbers is Prime map polynomial 6eef1ef7fe50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L273-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L273-L289

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_isPrime_map_polynomial_6eef1ef7fe50 (P : Ideal (MvPolynomial σ F)) [P.IsPrime] :
    (P.map (map (algebraMap F (Polynomial F)) : MvPolynomial σ F →+* _)).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«isPrime_map_polynomial» := P2M_GroundTheory_Heights__Heights_FieldNumbers_isPrime_map_polynomial_6eef1ef7fe50
