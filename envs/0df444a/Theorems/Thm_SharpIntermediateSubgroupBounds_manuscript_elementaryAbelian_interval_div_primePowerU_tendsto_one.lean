-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_interval_div_primePowerU_tendsto_one
-- name    : SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_interval_div_primePowerU_tendsto_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:07.632806+00:00
-- url     : https://prove2.me/theorems/b3111e6f-9c67-4811-ac74-446a09c0b262
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript elementary Abelian interval div prime Power U tendsto one
-- statement:
--   The elementary-abelian subgroup interval asymptotically exhausts the
--   finite prime-power envelope.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L150-L156
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L150-L156

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

theorem SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_interval_div_primePowerU_tendsto_one
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) /
        primePowerU p (2 * a)) atTop (nhds 1) := by sorry
