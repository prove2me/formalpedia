-- Prove2me | Theorems.Thm_Reformulated_AutPerF_CK_smul_coe
-- name    : Reformulated.AutPerF.CK.smul_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:22.86149+00:00
-- url     : https://prove2.me/theorems/3fd0de7c-c053-4d4a-b65e-2e292e5fe9f8
-- title:
--   CK: smul coe
-- statement:
--   The CK construction uses the smul coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean#L312-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean#L312-L313

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

theorem Reformulated.AutPerF.CK.smul_coe (g : GalK K) (x : AlgCl K) : g • (x : CK K) = (g x : AlgCl K) := by sorry
