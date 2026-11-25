-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_sum
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LB.lcg_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:48.825635+00:00
-- url     : https://prove2.me/theorems/32fb00ae-56bf-4baf-b58e-596818c55b2a
-- title:
--   LB: lcg sum
-- statement:
--   The LB construction uses the lcg sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L285-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L285-L291

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.LB.lcg_sum (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (j j' : K ⊕ K' → L.ι) :
    lcg L (Sum.elim φ φ') (Sum.elim ε ε') j j' =
      res (wchart_inl_le₂ L φ φ' j j') (lcg L φ ε (j ∘ Sum.inl) (j' ∘ Sum.inl)) *
        res (wchart_inr_le₂ L φ φ' j j') (lcg L φ' ε' (j ∘ Sum.inr) (j' ∘ Sum.inr)) := by sorry
