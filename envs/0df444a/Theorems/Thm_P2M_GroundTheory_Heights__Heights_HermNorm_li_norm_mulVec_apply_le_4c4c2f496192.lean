-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_mulVec_apply_le_4c4c2f496192
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_mulVec_apply_le_4c4c2f496192
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:50.900043+00:00
-- url     : https://prove2.me/theorems/6bf82d8f-492e-489d-9022-f1e10ad9bb2d
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm li norm mul Vec apply le 4c4c2f496192: P2 M Ground Theory Heights  Heights Herm Norm li norm mul Vec apply le 4c4c2f496192
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm li norm mul Vec apply le 4c4c2f496192 construction uses the P2 M Ground Theory Heights  Heights Herm Norm li norm mul Vec apply le 4c4c2f496192 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L33-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.HermNorm
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_mulVec_apply_le_4c4c2f496192 (h : HermNorm n) (v : Fin n → ℂ) (l : Fin n) :
    ‖(h.mat *ᵥ v) l‖ ≤ h.norm v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«li_norm_mulVec_apply_le» := P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_mulVec_apply_le_4c4c2f496192
