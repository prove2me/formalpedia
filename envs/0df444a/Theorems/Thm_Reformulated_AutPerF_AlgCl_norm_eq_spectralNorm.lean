-- Prove2me | Theorems.Thm_Reformulated_AutPerF_AlgCl_norm_eq_spectralNorm
-- name    : Reformulated.AutPerF.AlgCl.norm_eq_spectralNorm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:44.117917+00:00
-- url     : https://prove2.me/theorems/81731e3f-0928-475f-b590-17cfc456f60c
-- title:
--   Alg Cl: norm eq spectral Norm
-- statement:
--   The Alg Cl construction uses the norm eq spectral Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean#L269-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean#L269-L269

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
open Reformulated.AutPerF.AlgCl

theorem Reformulated.AutPerF.AlgCl.norm_eq_spectralNorm (x : AlgCl K) : ‖x‖ = spectralNorm K (AlgCl K) x := by sorry
