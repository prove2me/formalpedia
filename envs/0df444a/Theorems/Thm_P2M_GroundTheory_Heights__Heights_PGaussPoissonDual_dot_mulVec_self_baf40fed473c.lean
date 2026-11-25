-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussPoissonDual_dot_mulVec_self_baf40fed473c
-- name    : P2M_GroundTheory_Heights__Heights_PGaussPoissonDual_dot_mulVec_self_baf40fed473c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:58.243259+00:00
-- url     : https://prove2.me/theorems/0bf8c16c-1c9e-477d-b542-fb06a3e384fb
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Poisson Dual dot mul Vec self baf40fed473c: P2 M Ground Theory Heights  Heights PGauss Poisson Dual dot mul Vec self baf40fed473c
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Poisson Dual dot mul Vec self baf40fed473c construction uses the P2 M Ground Theory Heights  Heights PGauss Poisson Dual dot mul Vec self baf40fed473c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussPoissonDual.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussPoissonDual.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussPoissonDual
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
open Matrix Real
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussPoissonDual

theorem P2M_GroundTheory_Heights__Heights_PGaussPoissonDual_dot_mulVec_self_baf40fed473c {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℝ) :
    (B *ᵥ w) ⬝ᵥ (B *ᵥ w) = qf (Bᵀ * B) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussPoissonDual».«dot_mulVec_self» := P2M_GroundTheory_Heights__Heights_PGaussPoissonDual_dot_mulVec_self_baf40fed473c
