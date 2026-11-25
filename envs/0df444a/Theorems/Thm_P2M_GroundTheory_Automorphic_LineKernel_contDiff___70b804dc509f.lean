-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_contDiff___70b804dc509f
-- name    : P2M_GroundTheory_Automorphic_LineKernel_contDiff___70b804dc509f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:53.287452+00:00
-- url     : https://prove2.me/theorems/7318cfc9-2c80-4507-954c-3781be8bcfc0
-- title:
--   P2 M Ground Theory Automorphic Line Kernel cont Diff   70b804dc509f: P2 M Ground Theory Automorphic Line Kernel cont Diff   70b804dc509f
-- statement:
--   The P2 M Ground Theory Automorphic Line Kernel cont Diff   70b804dc509f construction uses the P2 M Ground Theory Automorphic Line Kernel cont Diff   70b804dc509f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L60-L66

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
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
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr

theorem P2M_GroundTheory_Automorphic_LineKernel_contDiff___70b804dc509f (n : ℕ) : ContDiff ℝ ∞ (ρ a r n) := by sorry

alias «GroundTheory».«Automorphic».«LineKernel».«contDiff_ρ» := P2M_GroundTheory_Automorphic_LineKernel_contDiff___70b804dc509f
