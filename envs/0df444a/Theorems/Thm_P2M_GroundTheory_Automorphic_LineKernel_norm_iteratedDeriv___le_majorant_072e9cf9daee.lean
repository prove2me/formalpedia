-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___le_majorant_072e9cf9daee
-- name    : P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___le_majorant_072e9cf9daee
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:58:09.487282+00:00
-- url     : https://prove2.me/theorems/1ea40e9a-922d-4c4e-bcc9-22936e440bb4
-- title:
--   P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv   le majorant 072e9cf9daee: P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv   le majorant 072e9cf9daee
-- statement:
--   The P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv   le majorant 072e9cf9daee construction uses the P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv   le majorant 072e9cf9daee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L158-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L158-L166

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
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
variable {M : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (hg : ∀ j, Good M ε j (a j))
include hε hg

theorem P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___le_majorant_072e9cf9daee (k j : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (ρ a (radii ε) j) t‖ ≤ majorant hε hg k j := by sorry

alias «GroundTheory».«Automorphic».«LineKernel».«norm_iteratedDeriv_ρ_le_majorant» := P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___le_majorant_072e9cf9daee
