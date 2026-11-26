-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_no_subquarter_elementaryAbelian_rpow_bound
-- name    : SharpIntermediateSubgroupBounds.manuscript_no_subquarter_elementaryAbelian_rpow_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:20.554164+00:00
-- url     : https://prove2.me/theorems/39ddbb53-038c-4a33-a0f8-ad90d9d8905b
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript no subquarter elementary Abelian rpow bound
-- statement:
--   The exponent `1/4` cannot be decreased, already on the standard
--   elementary-abelian subgroup intervals.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L201-L209
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L201-L209

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

theorem SharpIntermediateSubgroupBounds.manuscript_no_subquarter_elementaryAbelian_rpow_bound
    {p : ℕ} [Fact p.Prime] {alpha C : ℝ} (halpha : alpha < 1 / 4) :
    ¬ ∀ a : ℕ,
      (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤
        C * Real.rpow (p : ℝ) (4 * alpha * (a : ℝ) ^ 2) := by sorry
