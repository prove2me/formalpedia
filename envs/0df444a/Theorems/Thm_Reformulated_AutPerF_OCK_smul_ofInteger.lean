-- Prove2me | Theorems.Thm_Reformulated_AutPerF_OCK_smul_ofInteger
-- name    : Reformulated.AutPerF.OCK.smul_ofInteger
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:23.107802+00:00
-- url     : https://prove2.me/theorems/e853a345-6b9d-4ffa-ac54-37a27152aa86
-- title:
--   OCK: smul of Integer
-- statement:
--   The OCK construction uses the smul of Integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean#L320-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean#L320-L321

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
variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem Reformulated.AutPerF.OCK.smul_ofInteger (g : GalK K) (x : unitBall K) :
    g • OCK.ofInteger K x = OCK.ofInteger K x := by sorry
