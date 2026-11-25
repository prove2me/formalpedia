-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_linProj_comp_zeroExt_133519947d4f
-- name    : P2M_GroundTheory_Heights__Heights_det_linProj_comp_zeroExt_133519947d4f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:59.863989+00:00
-- url     : https://prove2.me/theorems/f48f1e79-08d2-4a9a-b33f-21bc4da828cc
-- title:
--   P2 M Ground Theory Heights  Heights det lin Proj comp zero Ext 133519947d4f: P2 M Ground Theory Heights  Heights det lin Proj comp zero Ext 133519947d4f
-- statement:
--   The P2 M Ground Theory Heights  Heights det lin Proj comp zero Ext 133519947d4f construction uses the P2 M Ground Theory Heights  Heights det lin Proj comp zero Ext 133519947d4f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadPlaneJac.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadPlaneJac.lean#L11-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadPlaneJac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadPlaneJac
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
noncomputable section
open Module

theorem P2M_GroundTheory_Heights__Heights_det_linProj_comp_zeroExt_133519947d4f {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ) :
    LinearMap.det ((linProjₗ π).comp (zeroExt m k)) = (coordPlaneBlock π).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«det_linProj_comp_zeroExt» := P2M_GroundTheory_Heights__Heights_det_linProj_comp_zeroExt_133519947d4f
