-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_integral_comp_mulVec_d6bc6b3375ff
-- name    : P2M_GroundTheory_Heights__Heights_KTheta_integral_comp_mulVec_d6bc6b3375ff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:02.464811+00:00
-- url     : https://prove2.me/theorems/9576f2ca-9333-53fd-8dcd-671305d440ac
-- title:
--   P2 M Ground Theory Heights  Heights KTheta integral comp mul Vec d6bc6b3375ff: P2 M Ground Theory Heights  Heights KTheta integral comp mul Vec d6bc6b3375ff
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta integral comp mul Vec d6bc6b3375ff construction uses the P2 M Ground Theory Heights  Heights KTheta integral comp mul Vec d6bc6b3375ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean#L30-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean#L30-L42

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

theorem P2M_GroundTheory_Heights__Heights_KTheta_integral_comp_mulVec_d6bc6b3375ff (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0)
    (f : (Fin g → ℝ) → ℝ) (hf : Continuous f) :
    ∫ v, f (B *ᵥ v) = |B.det|⁻¹ * ∫ x, f x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KTheta».«integral_comp_mulVec» := P2M_GroundTheory_Heights__Heights_KTheta_integral_comp_mulVec_d6bc6b3375ff
