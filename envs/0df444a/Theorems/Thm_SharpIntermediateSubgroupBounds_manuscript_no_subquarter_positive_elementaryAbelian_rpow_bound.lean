-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_no_subquarter_positive_elementaryAbelian_rpow_bound
-- name    : SharpIntermediateSubgroupBounds.manuscript_no_subquarter_positive_elementaryAbelian_rpow_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:46:13.604694+00:00
-- url     : https://prove2.me/theorems/fa53d78d-9e59-591b-8110-c89e7ad89a4a
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript no subquarter positive elementary Abelian rpow bound
-- statement:
--   Manuscript-domain form of exponent optimality.  A putative bound only on
--   positive ranks can be enlarged at the single rank-zero term, contradicting
--   the all-rank version above.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L214-L231
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L214-L231

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open Filter
noncomputable section
attribute [local instance] SharpIntermediateSubgroupBounds.manuscriptSubgroupIntervalFintype

theorem SharpIntermediateSubgroupBounds.manuscript_no_subquarter_positive_elementaryAbelian_rpow_bound
    {p : ℕ} [Fact p.Prime] {alpha C : ℝ} (halpha : alpha < 1 / 4) :
    ¬ ∀ a : ℕ, 0 < a →
      (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤
        C * Real.rpow (p : ℝ) (4 * alpha * (a : ℝ) ^ 2) := by sorry
