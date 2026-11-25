-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaFirstCoordSplit_term_le_3db75cf9db45
-- name    : P2M_GroundTheory_Heights__Heights_KThetaFirstCoordSplit_term_le_3db75cf9db45
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:10.129401+00:00
-- url     : https://prove2.me/theorems/308fbb44-c788-406f-8370-6485bf7efb74
-- title:
--   P2 M Ground Theory Heights  Heights KTheta First Coord Split term le 3db75cf9db45: P2 M Ground Theory Heights  Heights KTheta First Coord Split term le 3db75cf9db45
-- statement:
--   The P2 M Ground Theory Heights  Heights KTheta First Coord Split term le 3db75cf9db45 construction uses the P2 M Ground Theory Heights  Heights KTheta First Coord Split term le 3db75cf9db45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaFirstCoordSplit.lean#L13-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PThetaFirstCoordSplit.lean#L13-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaFirstCoordSplit
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
open GroundTheory.Heights₂.Heights.KThetaFirstCoordSplit

theorem P2M_GroundTheory_Heights__Heights_KThetaFirstCoordSplit_term_le_3db75cf9db45 {g : ℕ} [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) (a u₁ : Fin g → ℝ)
    (hY : Y.PosDef) (hρ : 0 < ρ) (hρY : Y⁻¹ 0 0 = ρ ^ 2) (k : Fin g → ℤ) :
    exp (-π * qf Y (intVec k + a + u₁)) ≤
      exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2) *
        exp (-(π / 2) * qf Y (intVec k + (a + u₁))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KThetaFirstCoordSplit».«term_le» := P2M_GroundTheory_Heights__Heights_KThetaFirstCoordSplit_term_le_3db75cf9db45
