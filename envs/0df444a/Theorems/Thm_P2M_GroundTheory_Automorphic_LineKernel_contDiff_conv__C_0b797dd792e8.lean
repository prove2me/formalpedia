-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_contDiff_conv__C_0b797dd792e8
-- name    : P2M_GroundTheory_Automorphic_LineKernel_contDiff_conv__C_0b797dd792e8
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:37.757042+00:00
-- url     : https://prove2.me/theorems/6b36a812-f9da-4301-b4f1-8fab7fc46fdf
-- title:
--   P2 M Ground Theory Automorphic Line Kernel cont Diff conv  C 0b797dd792e8: P2 M Ground Theory Automorphic Line Kernel cont Diff conv  C 0b797dd792e8
-- statement:
--   The P2 M Ground Theory Automorphic Line Kernel cont Diff conv  C 0b797dd792e8 construction uses the P2 M Ground Theory Automorphic Line Kernel cont Diff conv  C 0b797dd792e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L272-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L272-L277

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

theorem P2M_GroundTheory_Automorphic_LineKernel_contDiff_conv__C_0b797dd792e8 (n : ℕ) : ContDiff ℝ ∞ (KC a r n ⋆[mul ℂ ℂ] ηC a r (n + 1)) := by sorry

alias «GroundTheory».«Automorphic».«LineKernel».«contDiff_conv_ηC» := P2M_GroundTheory_Automorphic_LineKernel_contDiff_conv__C_0b797dd792e8
