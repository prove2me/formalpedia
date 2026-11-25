-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussPoissonDual_qf_smul_e74801869daa
-- name    : P2M_GroundTheory_Heights__Heights_PGaussPoissonDual_qf_smul_e74801869daa
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:53.373794+00:00
-- url     : https://prove2.me/theorems/cdfe6788-de33-4856-9f04-cfda128aa824
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Poisson Dual qf smul e74801869daa: P2 M Ground Theory Heights  Heights PGauss Poisson Dual qf smul e74801869daa
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Poisson Dual qf smul e74801869daa construction uses the P2 M Ground Theory Heights  Heights PGauss Poisson Dual qf smul e74801869daa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussPoissonDual.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussPoissonDual.lean#L13-L15

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

theorem P2M_GroundTheory_Heights__Heights_PGaussPoissonDual_qf_smul_e74801869daa {g : ℕ} (c : ℝ) (Y : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℝ) :
    qf (c • Y) w = c * qf Y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussPoissonDual».«qf_smul» := P2M_GroundTheory_Heights__Heights_PGaussPoissonDual_qf_smul_e74801869daa
