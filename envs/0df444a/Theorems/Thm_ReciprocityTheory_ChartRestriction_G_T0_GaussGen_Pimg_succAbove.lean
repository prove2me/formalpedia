-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_Pimg_succAbove
-- name    : ReciprocityTheory.ChartRestriction.G.T0.GaussGen.Pimg_succAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:21.525815+00:00
-- url     : https://prove2.me/theorems/39207dff-d6cf-41c3-826c-d8219feb274c
-- title:
--   Gauss Gen: Pimg succ Above
-- statement:
--   The Gauss Gen construction uses the Pimg succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/TranslSEquivApply.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/TranslSEquivApply.lean#L27-L30

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

theorem ReciprocityTheory.ChartRestriction.G.T0.GaussGen.Pimg_succAbove (j₀ : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) (k : Fin N) :
    Pimg j₀ x (i, j₀.succAbove k) = X (Sum.inr (i, k)) := by sorry
