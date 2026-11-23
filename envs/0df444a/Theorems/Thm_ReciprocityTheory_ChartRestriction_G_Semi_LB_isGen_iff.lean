-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LB.isGen_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:29.501798+00:00
-- url     : https://prove2.me/theorems/a7ec00ab-ec6f-4a62-a29e-3a24dc49850f
-- title:
--   LB: is Gen iff
-- statement:
--   The LB construction uses the is Gen iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L151-L155

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.LB.isGen_iff {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : Gen (LinComb L φ ε)) :
    t.IsGen ↔ ∀ i j : K → L.ι,
      res (inf_le_left : wchart L φ i ⊓ wchart L φ j ≤ wchart L φ i) (ts t i) =
        lcg L φ ε i j * res (inf_le_right : wchart L φ i ⊓ wchart L φ j ≤ wchart L φ j) (ts t j) := by sorry
