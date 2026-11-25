-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_qf_star_mul_self_975fe84e53ae
-- name    : P2M_GroundTheory_Heights__Heights_KTheta_qf_star_mul_self_975fe84e53ae
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:42.166749+00:00
-- url     : https://prove2.me/theorems/d8e4aaaf-ded3-4540-8f3a-62913dafe0f3
-- title:
--   P2 M Ground Theory Heights  Heights KTheta qf star mul self 975fe84e53ae: P2 M Ground Theory Heights  Heights KTheta qf star mul self 975fe84e53ae
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta qf star mul self 975fe84e53ae construction uses the P2 M Ground Theory Heights  Heights KTheta qf star mul self 975fe84e53ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean#L16-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix MeasureTheory Real
open scoped MatrixOrder
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KTheta
noncomputable section
variable {g : ℕ}

theorem P2M_GroundTheory_Heights__Heights_KTheta_qf_star_mul_self_975fe84e53ae (B : Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℝ) :
    qf (star B * B) v = ∑ i, (B *ᵥ v) i ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KTheta».«qf_star_mul_self» := P2M_GroundTheory_Heights__Heights_KTheta_qf_star_mul_self_975fe84e53ae
