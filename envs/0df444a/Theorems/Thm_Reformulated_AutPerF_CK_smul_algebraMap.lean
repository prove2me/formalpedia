-- Prove2me | Theorems.Thm_Reformulated_AutPerF_CK_smul_algebraMap
-- name    : Reformulated.AutPerF.CK.smul_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:33.691191+00:00
-- url     : https://prove2.me/theorems/3449e20b-34c3-4d08-ad62-2a952cf0751b
-- title:
--   CK: smul algebra Map
-- statement:
--   The CK construction uses the smul algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean#L315-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean#L315-L318

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

theorem Reformulated.AutPerF.CK.smul_algebraMap (g : GalK K) (x : K) :
    g • algebraMap K (CK K) x = algebraMap K (CK K) x := by sorry
