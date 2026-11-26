-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_interval_div_finiteUQ_tendsto_one
-- name    : SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_interval_div_finiteUQ_tendsto_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:12.701335+00:00
-- url     : https://prove2.me/theorems/9102b2a5-2202-5ce5-b8bc-bbf2bcacc4e5
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript elementary Abelian interval div finite UQ tendsto one
-- statement:
--   Literal finite-sum ratio, using the rational packing envelope evaluated
--   at the witness index.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L160-L173
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L160-L173

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

theorem SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_interval_div_finiteUQ_tendsto_one
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) /
        (((finiteUQ
          (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index p : ℚ) : ℝ)))
      atTop (nhds 1) := by sorry
