-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_dualNorm_pointOf_510e3d6db40f
-- name    : P2M_GroundTheory_Heights__Heights_ConeFsLog_dualNorm_pointOf_510e3d6db40f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:43.041217+00:00
-- url     : https://prove2.me/theorems/c5b4846d-d3a2-4287-a3c4-a4ba2e3dfdf9
-- title:
--   P2 M Ground Theory Heights  Heights Cone Fs Log dual Norm point Of 510e3d6db40f: P2 M Ground Theory Heights  Heights Cone Fs Log dual Norm point Of 510e3d6db40f
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Fs Log dual Norm point Of 510e3d6db40f construction uses the P2 M Ground Theory Heights  Heights Cone Fs Log dual Norm point Of 510e3d6db40f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFsLogIntegrable.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFsLogIntegrable.lean#L16-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSlab
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFsLogIntegrable
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
open MvPolynomial MeasureTheory Set Matrix Filter
noncomputable section
open GroundTheory.Heights₂.Heights.ConeFsLog
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ConeFsLog_dualNorm_pointOf_510e3d6db40f (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.dualNorm (h.pointOf y) = ‖y‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeFsLog».«dualNorm_pointOf» := P2M_GroundTheory_Heights__Heights_ConeFsLog_dualNorm_pointOf_510e3d6db40f
