-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_sub_2c1b4682dd90
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_sub_2c1b4682dd90
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:41.025853+00:00
-- url     : https://prove2.me/theorems/8ddd80ae-1f03-49c7-884c-478167444801
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers pull Deg sub 2c1b4682dd90: P2 M Ground Theory Heights  Heights Field Numbers pull Deg sub 2c1b4682dd90
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers pull Deg sub 2c1b4682dd90 construction uses the P2 M Ground Theory Heights  Heights Field Numbers pull Deg sub 2c1b4682dd90 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L150-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L150-L158

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
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
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)
variable [DecidableEq K] [DecidableEq K']
variable {F : Type u} [Field F]
omit [DecidableEq K] [DecidableEq K']

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_sub_2c1b4682dd90 (bf bg : K → ℕ) :
    pullDeg j (fun k => (bf k : ℤ) - bg k) =
      fun k' => ((Function.extend j bf 0 k' : ℕ) : ℤ) - ((Function.extend j bg 0 k' : ℕ) : ℤ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«pullDeg_sub» := P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_sub_2c1b4682dd90
