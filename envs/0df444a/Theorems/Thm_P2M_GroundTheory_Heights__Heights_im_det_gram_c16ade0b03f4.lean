-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_im_det_gram_c16ade0b03f4
-- name    : P2M_GroundTheory_Heights__Heights_im_det_gram_c16ade0b03f4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:05.131837+00:00
-- url     : https://prove2.me/theorems/815412fd-f49e-4b38-a107-0b23f1dc111e
-- title:
--   P2 M Ground Theory Heights  Heights im det gram c16ade0b03f4: P2 M Ground Theory Heights  Heights im det gram c16ade0b03f4
-- statement:
--   The P2 M Ground Theory Heights  Heights im det gram c16ade0b03f4 construction uses the P2 M Ground Theory Heights  Heights im det gram c16ade0b03f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L80-L82

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

theorem P2M_GroundTheory_Heights__Heights_im_det_gram_c16ade0b03f4 {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → V) :
    (det (gram ℂ w)).im = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«im_det_gram» := P2M_GroundTheory_Heights__Heights_im_det_gram_c16ade0b03f4
