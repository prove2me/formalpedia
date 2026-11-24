-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_contractPrime_7e3d9fd91401
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_contractPrime_7e3d9fd91401
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:35.910145+00:00
-- url     : https://prove2.me/theorems/f86d519f-692d-44ae-adf9-03ff9df6f021
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers is Multi Proj Prime contract Prime 7e3d9fd91401: P2 M Ground Theory Heights  Heights Field Numbers is Multi Proj Prime contract Prime 7e3d9fd91401
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers is Multi Proj Prime contract Prime 7e3d9fd91401 construction uses the P2 M Ground Theory Heights  Heights Field Numbers is Multi Proj Prime contract Prime 7e3d9fd91401 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L106-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L106-L122

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_contractPrime_7e3d9fd91401 {P' : Ideal (MRing ι' F)} (hP' : IsMultiProjPrime P') :
    IsMultiProjPrime (contractPrime j P') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«isMultiProjPrime_contractPrime» := P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_contractPrime_7e3d9fd91401
