-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_tsum_evenUSummand_eq_normalized_U
-- name    : SharpIntermediateSubgroupBounds.tsum_evenUSummand_eq_normalized_U
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:48:17.602255+00:00
-- url     : https://prove2.me/theorems/42dd440f-3b63-5842-9a20-0938a0c8dd98
-- title:
--   Sharp Intermediate Subgroup Bounds: tsum even USummand eq normalized U
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the tsum even USummand eq normalized U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L998-L1059
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L998-L1059

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.tsum_evenUSummand_eq_normalized_U {p a : ℕ} (hp : 2 ≤ p) :
    ∑' j : ℕ, evenUSummand p a j =
      (p : ℝ)⁻¹ ^ (a * a) * primePowerU p (2 * a) := by sorry
