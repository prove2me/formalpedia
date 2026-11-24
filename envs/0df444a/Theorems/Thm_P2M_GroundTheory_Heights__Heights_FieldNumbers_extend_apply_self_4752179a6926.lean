-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_apply_self_4752179a6926
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_apply_self_4752179a6926
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:38:51.423169+00:00
-- url     : https://prove2.me/theorems/3f56fec2-1cf1-4bcf-a794-30bd02108778
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers extend apply self 4752179a6926: P2 M Ground Theory Heights  Heights Field Numbers extend apply self 4752179a6926
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers extend apply self 4752179a6926 construction uses the P2 M Ground Theory Heights  Heights Field Numbers extend apply self 4752179a6926 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L20-L22

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_apply_self_4752179a6926 {M : Type*} [Zero M] (b : K → M) (k : K) :
    Function.extend j b 0 (j k) = b k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«extend_apply_self» := P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_apply_self_4752179a6926
