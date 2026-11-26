-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_qFactorial_cast_real_eq_pow_mul_gammaR
-- name    : SharpIntermediateSubgroupBounds.qFactorial_cast_real_eq_pow_mul_gammaR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:43:17.065777+00:00
-- url     : https://prove2.me/theorems/e730d094-884d-4041-bca0-6a50f3493a0d
-- title:
--   Sharp Intermediate Subgroup Bounds: q Factorial cast real eq pow mul gamma R
-- statement:
--   The finite Euler product is the normalized `q`-factorial.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L95-L102
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L95-L102

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.qFactorial_cast_real_eq_pow_mul_gammaR {q r : ℕ} (hq : 1 ≤ q) :
    (qFactorial q r : ℝ) = (q : ℝ) ^ qWeight r * gammaR (q : ℝ) r := by sorry
