-- Prove2me | Theorems.Thm_Reformulated_AutPerF_IsUnitBall_frobenius_surjective
-- name    : Reformulated.AutPerF.IsUnitBall.frobenius_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:33.71082+00:00
-- url     : https://prove2.me/theorems/76882686-3e71-429a-86d1-2b7d8a137dd8
-- title:
--   Is Unit Ball: frobenius surjective
-- statement:
--   The Is Unit Ball construction uses the frobenius surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean#L124-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean#L124-L129

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

theorem Reformulated.AutPerF.IsUnitBall.frobenius_surjective [IsAlgClosed C] [Fact p.Prime] :
    Function.Surjective (frobenius (ModP O p) p) := by sorry
