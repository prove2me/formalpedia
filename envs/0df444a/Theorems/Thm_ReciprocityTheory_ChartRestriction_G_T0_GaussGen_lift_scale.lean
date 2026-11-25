-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_lift_scale
-- name    : ReciprocityTheory.ChartRestriction.G.T0.GaussGen.lift_scale
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:45.636521+00:00
-- url     : https://prove2.me/theorems/6a3aca1c-9fb2-42af-ba2c-6bbe62a33d5e
-- title:
--   Gauss Gen: lift scale
-- statement:
--   The Gauss Gen construction uses the lift scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/TranslSEquivApply.lean#L74-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/TranslSEquivApply.lean#L74-L85

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

theorem ReciprocityTheory.ChartRestriction.G.T0.GaussGen.lift_scale {K : Type} [Field K] [CharZero K] [Algebra K Ω] (j₀ : Fin (N + 1))
    (x : Fin N → Ω) (b : Fin (D + 1)) (t : TVar D N) :
    diag (cS b (2 : Ω)) (Pimg j₀ x t) = aeval (Pimg j₀ x) (diag (cb b (2 : K)) (X t)) := by sorry
