-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_h0_pow_of_isMultiHomogeneous
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.h0_pow_of_isMultiHomogeneous
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:11.08627+00:00
-- url     : https://prove2.me/theorems/81019129-d5cf-555f-93dc-b0472e6aaa46
-- title:
--   Height Multiplicativity: h0 pow of is Multi Homogeneous
-- statement:
--   The Height Multiplicativity construction uses the h0 pow of is Multi Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDA.lean#L61-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDA.lean#L61-L72

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

theorem ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.h0_pow_of_isMultiHomogeneous {B n : ℕ} (hn : 0 < n) {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin n) K}
    (hf0 : f ≠ 0) (hf : IsMultiHomogeneous a f) (k : ℕ) : h0 (f ^ k) = k * h0 f := by sorry
