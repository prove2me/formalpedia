-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___succ_le_half_pow_5a11f0ddcc99
-- name    : P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___succ_le_half_pow_5a11f0ddcc99
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:46.158195+00:00
-- url     : https://prove2.me/theorems/260f7045-de16-446e-8da3-724ba1c5957e
-- title:
--   P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv   succ le half pow 5a11f0ddcc99: P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv   succ le half pow 5a11f0ddcc99
-- statement:
--   The P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv   succ le half pow 5a11f0ddcc99 construction uses the P2 M Ground Theory Automorphic Line Kernel norm iterated Deriv   succ le half pow 5a11f0ddcc99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L107-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L107-L138

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

theorem P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___succ_le_half_pow_5a11f0ddcc99 (n k : ℕ) (hk : k ≤ n + 1) (t : ℝ) :
    ‖iteratedDeriv k (ρ a (radii ε) (n + 1)) t‖ ≤ (1 / 2) ^ (n + 1) := by sorry

alias «GroundTheory».«Automorphic».«LineKernel».«norm_iteratedDeriv_ρ_succ_le_half_pow» := P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___succ_le_half_pow_5a11f0ddcc99
