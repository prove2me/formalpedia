-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv__C_ac13ffdbfcb3
-- name    : P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv__C_ac13ffdbfcb3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:12:54.469933+00:00
-- url     : https://prove2.me/theorems/9de471b4-a197-4e78-af3c-82a81db7df84
-- title:
--   P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv  C ac13ffdbfcb3: P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv  C ac13ffdbfcb3
-- statement:
--   The P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv  C ac13ffdbfcb3 construction uses the P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv  C ac13ffdbfcb3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L94-L98

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

theorem P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv__C_ac13ffdbfcb3 (j q : ℕ) (t : ℝ) :
    ‖iteratedDeriv q (ηC a r j) t‖ = ‖iteratedDeriv q (rem (a j) (r j)) t‖ := by sorry

alias «GroundTheory».«Automorphic».«LineKernel».«norm_iteratedDeriv_ηC» := P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv__C_ac13ffdbfcb3
