-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_finrank_quot
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.inh_finrank_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:06.151809+00:00
-- url     : https://prove2.me/theorems/a346ad28-e358-4801-8401-6af52ef68850
-- title:
--   I1: inh finrank quot
-- statement:
--   The I1 construction uses the inh finrank quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L276-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L276-L295

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {σ : Type*} {F : Type*} [Field F]

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.inh_finrank_quot (I : Ideal (MvPolynomial σ F)) (c : σ → F)
    (hI : I ≤ RingHom.ker (eval c)) (hX : ∀ s, X s - C (c s) ∈ I) :
    Module.finrank F (MvPolynomial σ F ⧸ I) = 1 := by sorry
