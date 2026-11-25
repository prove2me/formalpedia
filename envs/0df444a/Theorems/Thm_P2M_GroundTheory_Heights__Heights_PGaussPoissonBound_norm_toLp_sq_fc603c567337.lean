-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussPoissonBound_norm_toLp_sq_fc603c567337
-- name    : P2M_GroundTheory_Heights__Heights_PGaussPoissonBound_norm_toLp_sq_fc603c567337
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:35.243736+00:00
-- url     : https://prove2.me/theorems/3916fe8f-3224-4665-9f65-ddd7e7b7e507
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Poisson Bound norm to Lp sq fc603c567337: P2 M Ground Theory Heights  Heights PGauss Poisson Bound norm to Lp sq fc603c567337
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Poisson Bound norm to Lp sq fc603c567337 construction uses the P2 M Ground Theory Heights  Heights PGauss Poisson Bound norm to Lp sq fc603c567337 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussPoissonBound.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussPoissonBound.lean#L16-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussPoissonBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Real MeasureTheory
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussPoissonBound

theorem P2M_GroundTheory_Heights__Heights_PGaussPoissonBound_norm_toLp_sq_fc603c567337 {g : ℕ} (v : Fin g → ℝ) : ‖WithLp.toLp 2 v‖ ^ 2 = v ⬝ᵥ v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussPoissonBound».«norm_toLp_sq» := P2M_GroundTheory_Heights__Heights_PGaussPoissonBound_norm_toLp_sq_fc603c567337
