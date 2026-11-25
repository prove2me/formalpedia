-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_support___subset_41eb0b1e4540
-- name    : P2M_GroundTheory_Automorphic_LineKernel_support___subset_41eb0b1e4540
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:42.415837+00:00
-- url     : https://prove2.me/theorems/ada05ad1-dbab-4e05-be26-94da601a4a3f
-- title:
--   P2 M Ground Theory Automorphic Line Kernel support   subset 41eb0b1e4540: P2 M Ground Theory Automorphic Line Kernel support   subset 41eb0b1e4540
-- statement:
--   The P2 M Ground Theory Automorphic Line Kernel support   subset 41eb0b1e4540 construction uses the P2 M Ground Theory Automorphic Line Kernel support   subset 41eb0b1e4540 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L68-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L68-L92

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

theorem P2M_GroundTheory_Automorphic_LineKernel_support___subset_41eb0b1e4540 (n : ℕ) : support (ρ a r n) ⊆ Icc 0 (Rs r n) := by sorry

alias «GroundTheory».«Automorphic».«LineKernel».«support_ρ_subset» := P2M_GroundTheory_Automorphic_LineKernel_support___subset_41eb0b1e4540
