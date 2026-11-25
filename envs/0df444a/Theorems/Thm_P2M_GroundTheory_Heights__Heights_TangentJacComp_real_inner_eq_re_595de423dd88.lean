-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentJacComp_real_inner_eq_re_595de423dd88
-- name    : P2M_GroundTheory_Heights__Heights_TangentJacComp_real_inner_eq_re_595de423dd88
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:40:09.235901+00:00
-- url     : https://prove2.me/theorems/26580841-c31a-5091-bd66-5bb29d478f95
-- title:
--   P2 M Ground Theory Heights  Heights Tangent Jac Comp real inner eq re 595de423dd88: P2 M Ground Theory Heights  Heights Tangent Jac Comp real inner eq re 595de423dd88
-- statement:
--   The P2 M Ground Theory Heights  Heights Tangent Jac Comp real inner eq re 595de423dd88 construction uses the P2 M Ground Theory Heights  Heights Tangent Jac Comp real inner eq re 595de423dd88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentJacComp.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentJacComp.lean#L9-L11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacComp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentJacComp
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

theorem P2M_GroundTheory_Heights__Heights_TangentJacComp_real_inner_eq_re_595de423dd88 {d : ℕ} (x y : EuclideanSpace ℂ (Fin d)) :
    @inner ℝ _ _ x y = RCLike.re (@inner ℂ _ _ x y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TangentJacComp».«real_inner_eq_re» := P2M_GroundTheory_Heights__Heights_TangentJacComp_real_inner_eq_re_595de423dd88
