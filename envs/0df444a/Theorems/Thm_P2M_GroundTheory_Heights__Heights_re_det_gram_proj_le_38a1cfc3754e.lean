-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_re_det_gram_proj_le_38a1cfc3754e
-- name    : P2M_GroundTheory_Heights__Heights_re_det_gram_proj_le_38a1cfc3754e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:44.773874+00:00
-- url     : https://prove2.me/theorems/b79d350c-d2dc-45d6-b451-18b3814566d9
-- title:
--   P2 M Ground Theory Heights  Heights re det gram proj le 38a1cfc3754e: P2 M Ground Theory Heights  Heights re det gram proj le 38a1cfc3754e
-- statement:
--   The P2 M Ground Theory Heights  Heights re det gram proj le 38a1cfc3754e construction uses the P2 M Ground Theory Heights  Heights re det gram proj le 38a1cfc3754e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L143-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L143-L149

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open scoped ComplexOrder
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem P2M_GroundTheory_Heights__Heights_re_det_gram_proj_le_38a1cfc3754e {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Submodule ℂ V)
    [Y.HasOrthogonalProjection] (c : ι → V) :
    (det (gram ℂ fun i ↦ Y.starProjection (c i))).re ≤ (det (gram ℂ c)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«re_det_gram_proj_le» := P2M_GroundTheory_Heights__Heights_re_det_gram_proj_le_38a1cfc3754e
