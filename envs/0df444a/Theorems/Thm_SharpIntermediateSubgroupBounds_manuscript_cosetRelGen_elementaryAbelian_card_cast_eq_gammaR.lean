-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_cosetRelGen_elementaryAbelian_card_cast_eq_gammaR
-- name    : SharpIntermediateSubgroupBounds.manuscript_cosetRelGen_elementaryAbelian_card_cast_eq_gammaR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:02:24.796806+00:00
-- url     : https://prove2.me/theorems/3834edfc-1686-4f61-9c0f-2733695da70e
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript coset Rel Gen elementary Abelian card cast eq gamma R
-- statement:
--   Exact manuscript Remark 2.4 in its coset-tuple formulation.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L290-L310
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L290-L310

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

theorem SharpIntermediateSubgroupBounds.manuscript_cosetRelGen_elementaryAbelian_card_cast_eq_gammaR
    (p r : ℕ) [Fact p.Prime] :
    (Nat.card (CosetRelGen
      (⊥ : Subgroup (ElementaryAbelianGroup p r)) ⊤ r) : ℝ) =
      (p : ℝ) ^ (r * r) * gammaR (p : ℝ) r := by sorry
