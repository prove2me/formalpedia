-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_hasFDerivAt_partial_f6bd2ae7e203
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_hasFDerivAt_partial_f6bd2ae7e203
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:27:49.723267+00:00
-- url     : https://prove2.me/theorems/cb87ba56-93a7-48da-80f3-f0cf3baa054f
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free has FDeriv At partial f6bd2ae7e203: P2 M Ground Theory Heights  Heights Lower Bound Free has FDeriv At partial f6bd2ae7e203
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free has FDeriv At partial f6bd2ae7e203 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free has FDeriv At partial f6bd2ae7e203 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PFsPotLaplacian.lean#L43-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PFsPotLaplacian.lean#L43-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFsPotLaplacian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PFsPotLaplacian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open InnerProductSpace Laplacian Real MeasureTheory Filter Topology Set

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_hasFDerivAt_partial_f6bd2ae7e203 (y e : ℂ) :
    HasFDerivAt (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im))
      ((1 + ‖y‖ ^ 2)⁻¹ • (e.re • Complex.reCLM + e.im • Complex.imCLM) +
        (y.re * e.re + y.im * e.im) •
          (-(((1 + ‖y‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ y))) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«hasFDerivAt_partial» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_hasFDerivAt_partial_f6bd2ae7e203
