-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_contDiff__C_d6b9b6ae5dcf
-- name    : P2M_GroundTheory_Automorphic_LineKernel_contDiff__C_d6b9b6ae5dcf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:22.568805+00:00
-- url     : https://prove2.me/theorems/bd06a21e-4644-4e31-bfb1-794d57650401
-- title:
--   P2 M Ground Theory Automorphic Line Kernel cont Diff  C d6b9b6ae5dcf: P2 M Ground Theory Automorphic Line Kernel cont Diff  C d6b9b6ae5dcf
-- statement:
--   The P2 M Ground Theory Automorphic Line Kernel cont Diff  C d6b9b6ae5dcf construction uses the P2 M Ground Theory Automorphic Line Kernel cont Diff  C d6b9b6ae5dcf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L216-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L216-L217

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

theorem P2M_GroundTheory_Automorphic_LineKernel_contDiff__C_d6b9b6ae5dcf (a r : ℕ → ℝ) (j : ℕ) : ContDiff ℝ ∞ (ηC a r j) := by sorry

alias «GroundTheory».«Automorphic».«LineKernel».«contDiff_ηC» := P2M_GroundTheory_Automorphic_LineKernel_contDiff__C_d6b9b6ae5dcf
