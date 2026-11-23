-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_Pimg_self
-- name    : ReciprocityTheory.ChartRestriction.G.T0.GaussGen.Pimg_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:30.858588+00:00
-- url     : https://prove2.me/theorems/66b669a3-4459-4746-8d1e-c293edf4f934
-- title:
--   Gauss Gen: Pimg self
-- statement:
--   The Gauss Gen construction uses the Pimg self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/TranslSEquivApply.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/TranslSEquivApply.lean#L21-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_TranslSEquivApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.GaussGen
open MvPolynomial NumberField BlockPoly
variable {Ω : Type} [Field Ω] {D N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.GaussGen.Pimg_self (j₀ : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) :
    Pimg j₀ x (i, j₀) =
      if i = 0 then X (Sum.inl ()) else -∑ k, X (Sum.inr (i, k)) * C (x k) := by sorry
