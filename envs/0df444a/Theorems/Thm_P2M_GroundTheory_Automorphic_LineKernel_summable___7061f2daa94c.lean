-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_summable___7061f2daa94c
-- name    : P2M_GroundTheory_Automorphic_LineKernel_summable___7061f2daa94c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:35.942107+00:00
-- url     : https://prove2.me/theorems/76507e4e-0afd-5aac-bfc1-9ce8c30144e3
-- title:
--   P2 M Ground Theory Automorphic Line Kernel summable   7061f2daa94c: P2 M Ground Theory Automorphic Line Kernel summable   7061f2daa94c
-- statement:
--   The P2 M Ground Theory Automorphic Line Kernel summable   7061f2daa94c construction uses the P2 M Ground Theory Automorphic Line Kernel summable   7061f2daa94c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L178-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L178-L180

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

theorem P2M_GroundTheory_Automorphic_LineKernel_summable___7061f2daa94c (t : ℝ) : Summable fun j => ρ a (radii ε) j t := by sorry

alias «GroundTheory».«Automorphic».«LineKernel».«summable_ρ» := P2M_GroundTheory_Automorphic_LineKernel_summable___7061f2daa94c
