-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- name    : ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:12.743718+00:00
-- url     : https://prove2.me/theorems/454b8cfa-97dd-4781-af42-0471ac197158
-- title:
--   Gauss Gen: transl SEquiv apply
-- statement:
--   The Gauss Gen construction uses the transl SEquiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/TranslSEquivApply.lean#L121-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/TranslSEquivApply.lean#L121-L122

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

theorem ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply (j₀ : Fin (N + 1)) (a : Fin (N + 1) → Ω)
    (g : MvPolynomial (SVar D N) Ω) : translSEquiv j₀ a g = translS j₀ a g := by sorry

attribute [defeq] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply
