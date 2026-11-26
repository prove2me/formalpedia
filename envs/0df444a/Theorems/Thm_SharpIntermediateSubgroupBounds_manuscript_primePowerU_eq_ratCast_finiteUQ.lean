-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_primePowerU_eq_ratCast_finiteUQ
-- name    : SharpIntermediateSubgroupBounds.manuscript_primePowerU_eq_ratCast_finiteUQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:50:43.0821+00:00
-- url     : https://prove2.me/theorems/605b9734-8d23-537d-ab4b-9de951b2371c
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript prime Power U eq rat Cast finite UQ
-- statement:
--   On a prime power, the manuscript's real envelope is exactly the real
--   cast of the rational finite packing sum.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L92-L117
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L92-L117

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

theorem SharpIntermediateSubgroupBounds.manuscript_primePowerU_eq_ratCast_finiteUQ
    (p n : ℕ) (hp : 1 < p) :
    primePowerU p n = ((finiteUQ (p ^ n) p : ℚ) : ℝ) := by sorry
