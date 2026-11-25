-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_empty_cocycle
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LB.lcg_empty_cocycle
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:01.177122+00:00
-- url     : https://prove2.me/theorems/d37d16c7-8627-4067-9162-02713a917443
-- title:
--   LB: lcg empty cocycle
-- statement:
--   The LB construction uses the lcg empty cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L198-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L198-L210

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
variable (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.Semi.LB.lcg_empty_cocycle (a b c : PEmpty.{u+1} → L.ι) :
    res (inf_le_left : wchart L (Y := Y) PEmpty.elim a ⊓ wchart L PEmpty.elim b ⊓
        wchart L PEmpty.elim c ≤ wchart L PEmpty.elim a ⊓ wchart L PEmpty.elim b)
        (lcg L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim a b) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        wchart L (Y := Y) PEmpty.elim a ⊓ wchart L PEmpty.elim b ⊓ wchart L PEmpty.elim c ≤
          wchart L PEmpty.elim b ⊓ wchart L PEmpty.elim c)
        (lcg L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim b c) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        wchart L (Y := Y) PEmpty.elim a ⊓ wchart L PEmpty.elim b ⊓ wchart L PEmpty.elim c ≤
          wchart L PEmpty.elim a ⊓ wchart L PEmpty.elim c)
        (lcg L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim a c) := by sorry
