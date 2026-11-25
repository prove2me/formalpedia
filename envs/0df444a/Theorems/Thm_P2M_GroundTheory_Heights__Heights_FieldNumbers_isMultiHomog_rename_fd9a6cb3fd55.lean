-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_rename_fd9a6cb3fd55
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_rename_fd9a6cb3fd55
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:48.772407+00:00
-- url     : https://prove2.me/theorems/352999a8-6793-4b4f-950a-b1620fd8936b
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog rename fd9a6cb3fd55: P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog rename fd9a6cb3fd55
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog rename fd9a6cb3fd55 construction uses the P2 M Ground Theory Heights  Heights Field Numbers is Multi Homog rename fd9a6cb3fd55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L75-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L75-L84

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_rename_fd9a6cb3fd55 {a : MRing (fun k => ι' (j k)) F} {c : K → ℕ} (ha : IsMultiHomog a c) :
    IsMultiHomog (rename (blockIncl j ι') a) (Function.extend j c 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«isMultiHomog_rename» := P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_rename_fd9a6cb3fd55
