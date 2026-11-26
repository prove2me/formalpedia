-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_antitone
-- name    : SharpIntermediateSubgroupBounds.gammaR_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:22.557144+00:00
-- url     : https://prove2.me/theorems/0b2e947a-aaa4-4f2e-8c01-4400916270f2
-- title:
--   Sharp Intermediate Subgroup Bounds: gamma R antitone
-- statement:
--   Finite Euler products decrease as more factors are included.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L48-L54
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L48-L54

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.gammaR_antitone {p : ℝ} (hp : 1 < p) : Antitone (gammaR p) := by sorry
