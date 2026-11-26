-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_frameProd_diagonal_cast_real_eq_gammaR
-- name    : SharpIntermediateSubgroupBounds.frameProd_diagonal_cast_real_eq_gammaR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:22.700541+00:00
-- url     : https://prove2.me/theorems/fbb975e2-da50-4e25-9d4b-5d84bd386cd0
-- title:
--   Sharp Intermediate Subgroup Bounds: frame Prod diagonal cast real eq gamma R
-- statement:
--   The exact Euler-product form of the ordered-basis count.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L174-L183
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L174-L183

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.frameProd_diagonal_cast_real_eq_gammaR {p r : ℕ} (hp : 2 ≤ p) :
    (frameProd p r r : ℝ) =
      (p : ℝ) ^ (r * r) * gammaR (p : ℝ) r := by sorry
