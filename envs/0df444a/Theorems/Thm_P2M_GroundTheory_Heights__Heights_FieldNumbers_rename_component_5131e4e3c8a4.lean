-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_component_5131e4e3c8a4
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_component_5131e4e3c8a4
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:01.300128+00:00
-- url     : https://prove2.me/theorems/ea552255-afcd-4356-9bf8-09521eb8abcc
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers rename component 5131e4e3c8a4: P2 M Ground Theory Heights  Heights Field Numbers rename component 5131e4e3c8a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers rename component 5131e4e3c8a4 construction uses the P2 M Ground Theory Heights  Heights Field Numbers rename component 5131e4e3c8a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L86-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L86-L104

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_component_5131e4e3c8a4 (a : MRing (fun k => ι' (j k)) F) (b : K → ℕ) :
    rename (blockIncl j ι') (weightedHomogeneousComponent (blockWeight (fun k => ι' (j k))) b a) =
      weightedHomogeneousComponent (blockWeight ι') (Function.extend j b 0)
        (rename (blockIncl j ι') a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«rename_component» := P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_component_5131e4e3c8a4
