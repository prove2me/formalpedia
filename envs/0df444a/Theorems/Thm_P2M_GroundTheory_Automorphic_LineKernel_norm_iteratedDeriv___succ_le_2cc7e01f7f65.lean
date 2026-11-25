-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___succ_le_2cc7e01f7f65
-- name    : P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___succ_le_2cc7e01f7f65
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:00.527921+00:00
-- url     : https://prove2.me/theorems/ebe4c42a-7752-4aa9-b1e1-c80b6b64f769
-- title:
--   P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv   succ le 2cc7e01f7f65: P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv   succ le 2cc7e01f7f65
-- statement:
--   The P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv   succ le 2cc7e01f7f65 construction uses the P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv   succ le 2cc7e01f7f65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L100-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L100-L141

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

theorem P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___succ_le_2cc7e01f7f65 (n m : ℕ) {B : ℕ → ℝ}
    (hB : ∀ q t, ‖iteratedDeriv q (rem (a (n + 1)) (r (n + 1))) t‖ ≤ B q) (t : ℝ) :
    ‖iteratedDeriv m (ρ a r (n + 1)) t‖ ≤
      ∑ p ∈ Finset.range (n + 2), coef a (n + 1) p * B (p + m) := by sorry

alias «GroundTheory».«Automorphic».«LineKernel».«norm_iteratedDeriv_ρ_succ_le» := P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___succ_le_2cc7e01f7f65
