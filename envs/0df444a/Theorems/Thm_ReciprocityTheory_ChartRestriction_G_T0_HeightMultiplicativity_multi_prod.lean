-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_multi_prod
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.multi_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:35:50.813565+00:00
-- url     : https://prove2.me/theorems/9b73d48d-3e3e-4b58-94c6-ffa263e31f54
-- title:
--   Height Multiplicativity: multi prod
-- statement:
--   The Height Multiplicativity construction uses the multi prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDA.lean#L47-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDA.lean#L47-L57

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
open MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed

theorem ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.multi_prod {R : Type*} [CommSemiring R] {B n : ℕ} {α : Type*} (s : Finset α)
    (e : α → Fin B → ℕ) (f : α → MvPolynomial (Fin B × Fin n) R)
    (hf : ∀ i ∈ s, IsMultiHomogeneous (e i) (f i)) :
    IsMultiHomogeneous (∑ i ∈ s, e i) (∏ i ∈ s, f i) := by sorry
