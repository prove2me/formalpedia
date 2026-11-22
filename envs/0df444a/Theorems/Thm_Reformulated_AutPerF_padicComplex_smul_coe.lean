-- Prove2me | Theorems.Thm_Reformulated_AutPerF_padicComplex_smul_coe
-- name    : Reformulated.AutPerF.padicComplex_smul_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:30.499956+00:00
-- url     : https://prove2.me/theorems/68cfce1a-2cb0-4e75-8e05-d1a58b7afd3f
-- title:
--   Aut Per F: padic Complex smul coe
-- statement:
--   The Aut Per F construction uses the padic Complex smul coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean#L222-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/UniformContinuousConstSMulOfIsIsometricSMul.lean#L222-L225

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
variable (p : ℕ) [Fact p.Prime]

theorem Reformulated.AutPerF.padicComplex_smul_coe {K : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
    [IsScalarTower ℚ_[p] K (PadicAlgCl p)] (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p)
    (x : PadicAlgCl p) : g • (x : ℂ_[p]) = (g x : PadicAlgCl p) := by sorry
