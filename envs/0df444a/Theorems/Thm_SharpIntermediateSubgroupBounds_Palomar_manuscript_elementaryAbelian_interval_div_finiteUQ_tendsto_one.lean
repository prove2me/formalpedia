-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_Palomar_manuscript_elementaryAbelian_interval_div_finiteUQ_tendsto_one
-- name    : SharpIntermediateSubgroupBounds.Palomar.manuscript_elementaryAbelian_interval_div_finiteUQ_tendsto_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:05:00.976891+00:00
-- url     : https://prove2.me/theorems/b2370470-df12-5bac-b2d9-5eee4034b80a
-- title:
--   Palomar: manuscript elementary Abelian interval div finite UQ tendsto one
-- statement:
--   Palomar-facing `Nat.card` form of the finite-envelope asymptotic.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/Solution.lean#L46-L55
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/Solution.lean#L46-L55

import Definitions.Def_SharpIntermediateSubgroupBounds
import Definitions.Def_SharpIntermediateSubgroupBounds_Solution
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_interval_div_finiteUQ_tendsto_one

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open SharpIntermediateSubgroupBounds.Palomar
open scoped BigOperators Topology
open Filter Finset Real
noncomputable section

theorem SharpIntermediateSubgroupBounds.Palomar.manuscript_elementaryAbelian_interval_div_finiteUQ_tendsto_one
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (Nat.card (elementaryAbelianInterval p (2 * a)) : ℝ) /
        (((finiteUQ
          (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index p : ℚ) : ℝ)))
      atTop (nhds 1) := by sorry
