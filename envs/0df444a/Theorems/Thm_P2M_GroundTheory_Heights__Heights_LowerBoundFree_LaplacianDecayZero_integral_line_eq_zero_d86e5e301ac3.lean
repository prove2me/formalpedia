-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_LaplacianDecayZero_integral_line_eq_zero_d86e5e301ac3
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_LaplacianDecayZero_integral_line_eq_zero_d86e5e301ac3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:28:03.081296+00:00
-- url     : https://prove2.me/theorems/51abd7d8-4d34-4b8e-99f1-b6c9d252bb31
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Laplacian Decay Zero integral line eq zero d86e5e301ac3: P2 M Ground Theory Heights  Heights Lower Bound Free Laplacian Decay Zero integral line eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Laplacian Decay Zero integral line eq zero d86e5e301ac3 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Laplacian Decay Zero integral line eq zero d86e5e301ac3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PLaplacianDecayZero.lean#L11-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PLaplacianDecayZero.lean#L11-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsLaplacianDecayZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PLaplacianDecayZero
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
open InnerProductSpace Laplacian MeasureTheory Filter Topology

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_LaplacianDecayZero_integral_line_eq_zero_d86e5e301ac3 (v : ℂ → ℝ)
    (hdiff : Differentiable ℝ (fderiv ℝ v))
    (hlim : Tendsto (fderiv ℝ v) (cocompact ℂ) (𝓝 0)) (w e : ℂ) (he : ‖e‖ = 1) :
    ∫ t : ℝ, fderiv ℝ (fderiv ℝ v) (w + (t : ℂ) * e) e e = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«LaplacianDecayZero».«integral_line_eq_zero» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_LaplacianDecayZero_integral_line_eq_zero_d86e5e301ac3
