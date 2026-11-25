-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_dg_cocycle
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LB.dg_cocycle
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:46.278232+00:00
-- url     : https://prove2.me/theorems/c66d4b9b-4966-4ee4-9d50-c497a945ae2e
-- title:
--   LB: dg cocycle
-- statement:
--   The LB construction uses the dg cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L106-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L106-L116

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open ReciprocityTheory.ChartRestriction.G.Semi.LB
variable {X Y Z : Scheme.{u}}

theorem ReciprocityTheory.ChartRestriction.G.Semi.LB.dg_cocycle {M L : LB X} (hM : M.IsLB) (hL : L.IsLB) (p q r : M.ι × L.ι) :
    res (inf_le_left : M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ⊓ (M.U r.1 ⊓ L.U r.2) ≤
        M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2)) (dg M L p q) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ⊓ (M.U r.1 ⊓ L.U r.2) ≤
          M.U q.1 ⊓ L.U q.2 ⊓ (M.U r.1 ⊓ L.U r.2)) (dg M L q r) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ⊓ (M.U r.1 ⊓ L.U r.2) ≤
          M.U p.1 ⊓ L.U p.2 ⊓ (M.U r.1 ⊓ L.U r.2)) (dg M L p r) := by sorry
