-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_qBinom_cast_real_eq_gammaR
-- name    : SharpIntermediateSubgroupBounds.qBinom_cast_real_eq_gammaR
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:43:22.612796+00:00
-- url     : https://prove2.me/theorems/4309233e-9aa3-4efe-8b0c-0e87b249a8c5
-- title:
--   Sharp Intermediate Subgroup Bounds: q Binom cast real eq gamma R
-- statement:
--   Gaussian product formula in terms of finite Euler products.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L105-L140
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L105-L140

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.qBinom_cast_real_eq_gammaR {q n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    (qBinom q n k : ℝ) =
      (q : ℝ) ^ (k * (n - k)) * gammaR (q : ℝ) n /
        (gammaR (q : ℝ) k * gammaR (q : ℝ) (n - k)) := by sorry
