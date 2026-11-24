-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_smul_947f2ff938a9
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_smul_947f2ff938a9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:21.733388+00:00
-- url     : https://prove2.me/theorems/a6b21ec5-6e7f-4e49-8985-8828f0914c14
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm dual Norm smul 947f2ff938a9: P2 M Ground Theory Heights  Heights Herm Norm dual Norm smul 947f2ff938a9
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm dual Norm smul 947f2ff938a9 construction uses the P2 M Ground Theory Heights  Heights Herm Norm dual Norm smul 947f2ff938a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFsLogSmul.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFsLogSmul.lean#L9-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
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

theorem P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_smul_947f2ff938a9 {n : ℕ} (h : HermNorm n) (t : ℂ) (y : Fin n → ℂ) :
    h.dualNorm (t • y) = ‖t‖ * h.dualNorm y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«dualNorm_smul» := P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_smul_947f2ff938a9
