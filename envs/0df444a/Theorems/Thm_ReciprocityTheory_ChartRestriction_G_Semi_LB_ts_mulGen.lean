-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_ts_mulGen
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LB.ts_mulGen
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:36.813929+00:00
-- url     : https://prove2.me/theorems/dc7bb86c-66e0-4b18-980b-f0d22d42b145
-- title:
--   LB: ts mul Gen
-- statement:
--   The LB construction uses the ts mul Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L279-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L279-L283

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.LB.ts_mulGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : Gen (LinComb L φ ε)) (t' : Gen (LinComb L φ' ε')) (j : K ⊕ K' → L.ι) :
    ts (mulGen L φ ε φ' ε' t t') j =
      res (wchart_inl_le L φ φ' j) (ts t (j ∘ Sum.inl)) *
        res (wchart_inr_le L φ φ' j) (ts t' (j ∘ Sum.inr)) := by sorry
