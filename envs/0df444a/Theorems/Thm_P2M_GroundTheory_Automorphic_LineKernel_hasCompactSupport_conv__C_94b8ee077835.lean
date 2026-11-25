-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_hasCompactSupport_conv__C_94b8ee077835
-- name    : P2M_GroundTheory_Automorphic_LineKernel_hasCompactSupport_conv__C_94b8ee077835
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:10.902553+00:00
-- url     : https://prove2.me/theorems/9da56cb1-3520-4071-8837-a06fa8eec1b5
-- title:
--   P2 M Ground Theory Automorphic Line Kernel has Compact Support conv  C 94b8ee077835: P2 M Ground Theory Automorphic Line Kernel has Compact Support conv  C 94b8ee077835
-- statement:
--   The P2 M Ground Theory Automorphic Line Kernel has Compact Support conv  C 94b8ee077835 construction uses the P2 M Ground Theory Automorphic Line Kernel has Compact Support conv  C 94b8ee077835 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L279-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L279-L281

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr

theorem P2M_GroundTheory_Automorphic_LineKernel_hasCompactSupport_conv__C_94b8ee077835 (n : ℕ) :
    HasCompactSupport (KC a r n ⋆[mul ℂ ℂ] ηC a r (n + 1)) := by sorry

alias «GroundTheory».«Automorphic».«LineKernel».«hasCompactSupport_conv_ηC» := P2M_GroundTheory_Automorphic_LineKernel_hasCompactSupport_conv__C_94b8ee077835
