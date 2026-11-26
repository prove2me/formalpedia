-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_qWeight_split
-- name    : SharpIntermediateSubgroupBounds.qWeight_split
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:47:21.367794+00:00
-- url     : https://prove2.me/theorems/97052e6e-b8c9-4702-8087-44dccccb4552
-- title:
--   Sharp Intermediate Subgroup Bounds: q Weight split
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the q Weight split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L65-L83
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L65-L83

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.qWeight_split : ∀ {n k : ℕ}, k ≤ n →
    qWeight n = qWeight k + qWeight (n - k) + k * (n - k) := by sorry
