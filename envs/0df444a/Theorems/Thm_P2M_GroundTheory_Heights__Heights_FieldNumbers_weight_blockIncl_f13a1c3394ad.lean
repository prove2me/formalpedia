-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_blockIncl_f13a1c3394ad
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_blockIncl_f13a1c3394ad
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:17.744067+00:00
-- url     : https://prove2.me/theorems/f1308e09-08ff-4a52-8593-f80a279ba802
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers weight block Incl f13a1c3394ad: P2 M Ground Theory Heights  Heights Field Numbers weight block Incl f13a1c3394ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers weight block Incl f13a1c3394ad construction uses the P2 M Ground Theory Heights  Heights Field Numbers weight block Incl f13a1c3394ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L50-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L50-L71

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_blockIncl_f13a1c3394ad (d : (Σ k, ι' (j k)) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain (blockIncl j ι') d) =
      Function.extend j (Finsupp.weight (blockWeight (fun k => ι' (j k))) d) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«weight_blockIncl» := P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_blockIncl_f13a1c3394ad
