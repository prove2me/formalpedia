-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_hasCompactSupport__C_147c0388f3f8
-- name    : P2M_GroundTheory_Automorphic_LineKernel_hasCompactSupport__C_147c0388f3f8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:21.254738+00:00
-- url     : https://prove2.me/theorems/f2c485c9-49cc-4f07-9f2f-2c62eb8e5e73
-- title:
--   P2 M Ground Theory Automorphic Line Kernel has Compact Support  C 147c0388f3f8: P2 M Ground Theory Automorphic Line Kernel has Compact Support  C 147c0388f3f8
-- statement:
--   The P2 M Ground Theory Automorphic Line Kernel has Compact Support  C 147c0388f3f8 construction uses the P2 M Ground Theory Automorphic Line Kernel has Compact Support  C 147c0388f3f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L224-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L224-L225

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

theorem P2M_GroundTheory_Automorphic_LineKernel_hasCompactSupport__C_147c0388f3f8 (j : ℕ) : HasCompactSupport (ηC a r j) := by sorry

alias «GroundTheory».«Automorphic».«LineKernel».«hasCompactSupport_ηC» := P2M_GroundTheory_Automorphic_LineKernel_hasCompactSupport__C_147c0388f3f8
