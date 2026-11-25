-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_logHeight_prod_pow
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.logHeight_prod_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:21.672108+00:00
-- url     : https://prove2.me/theorems/51828500-3e7b-486f-803a-da0aef878423
-- title:
--   Height Multiplicativity: log Height prod pow
-- statement:
--   The Height Multiplicativity construction uses the log Height prod pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDA.lean#L74-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDA.lean#L74-L96

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
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.logHeight_prod_pow {B n : ℕ} (hn : 0 < n) {α : Type*} (s : Finset α) (e : α → Fin B → ℕ)
    (f : α → MvPolynomial (Fin B × Fin n) K) (k : α → ℕ)
    (hf0 : ∀ i ∈ s, f i ≠ 0) (hf : ∀ i ∈ s, IsMultiHomogeneous (e i) (f i)) :
    h0 (∏ i ∈ s, f i ^ k i) = ∑ i ∈ s, (k i : ℝ) * h0 (f i) := by sorry
