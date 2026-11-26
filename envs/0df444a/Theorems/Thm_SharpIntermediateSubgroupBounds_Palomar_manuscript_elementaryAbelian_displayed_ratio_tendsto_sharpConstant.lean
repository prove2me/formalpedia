-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_Palomar_manuscript_elementaryAbelian_displayed_ratio_tendsto_sharpConstant
-- name    : SharpIntermediateSubgroupBounds.Palomar.manuscript_elementaryAbelian_displayed_ratio_tendsto_sharpConstant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:03:43.6973+00:00
-- url     : https://prove2.me/theorems/51e6a78f-1c47-4050-9c82-70deacfaf351
-- title:
--   Palomar: manuscript elementary Abelian displayed ratio tendsto sharp Constant
-- statement:
--   Palomar-facing `Nat.card` form of the elementary-abelian displayed-ratio
--   limit.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/Solution.lean#L33-L43
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/Solution.lean#L33-L43

import Definitions.Def_SharpIntermediateSubgroupBounds
import Definitions.Def_SharpIntermediateSubgroupBounds_Solution
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_displayed_ratio_tendsto_sharpConstant

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open SharpIntermediateSubgroupBounds.Palomar
open scoped BigOperators Topology
open Filter Finset Real
noncomputable section

theorem SharpIntermediateSubgroupBounds.Palomar.manuscript_elementaryAbelian_displayed_ratio_tendsto_sharpConstant
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (Nat.card (elementaryAbelianInterval p (2 * a)) : ℝ) /
        (((⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index : ℝ) ^
          (indexLog p
            (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index / 4)))
      atTop (nhds (sharpConstant (p : ℝ))) := by sorry
