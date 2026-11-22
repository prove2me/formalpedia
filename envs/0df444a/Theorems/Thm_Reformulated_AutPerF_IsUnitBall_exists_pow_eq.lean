-- Prove2me | Theorems.Thm_Reformulated_AutPerF_IsUnitBall_exists_pow_eq
-- name    : Reformulated.AutPerF.IsUnitBall.exists_pow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:14.291434+00:00
-- url     : https://prove2.me/theorems/daad9a34-a87f-4ca3-8ec2-acdd2242884f
-- title:
--   Is Unit Ball: exists pow eq
-- statement:
--   The Is Unit Ball construction uses the exists pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean#L118-L122

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal Filter Topology
open Reformulated Reformulated.AutPerF
universe u v
open Reformulated.AutPerF.IsUnitBall
variable {C : Type u} [NormedField C] (O : ValuationSubring C) [IsUnitBall O]
variable (p : ℕ)
variable [hp : Fact (‖(p : C)‖ < 1)]
omit hp

theorem Reformulated.AutPerF.IsUnitBall.exists_pow_eq [IsAlgClosed C] (x : O) {n : ℕ} (hn : 0 < n) : ∃ y : O, y ^ n = x := by sorry
