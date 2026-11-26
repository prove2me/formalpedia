-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_card_generatingFrames_fin_zmod_cast_eq_gammaR
-- name    : SharpIntermediateSubgroupBounds.card_generatingFrames_fin_zmod_cast_eq_gammaR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:32.154919+00:00
-- url     : https://prove2.me/theorems/2d0b0003-9a72-489c-b953-be83513fb505
-- title:
--   Sharp Intermediate Subgroup Bounds: card generating Frames fin zmod cast eq gamma R
-- statement:
--   Exact cardinality of the generating tuples in the elementary-abelian
--   escape family.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L271-L275
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L271-L275

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.card_generatingFrames_fin_zmod_cast_eq_gammaR (p r : ℕ) [Fact p.Prime] :
    (Nat.card (GeneratingFramesFinZMod p r) : ℝ) =
      (p : ℝ) ^ (r * r) * gammaR (p : ℝ) r := by sorry
