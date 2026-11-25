-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_multi_pow
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.multi_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:35:52.730777+00:00
-- url     : https://prove2.me/theorems/1e4b83cc-660c-47dd-bb7e-93a8b6eae6e0
-- title:
--   Height Multiplicativity: multi pow
-- statement:
--   The Height Multiplicativity construction uses the multi pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDA.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDA.lean#L38-L45

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

theorem ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.multi_pow {R : Type*} [CommSemiring R] {B n : ℕ} {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin n) R} (hf : IsMultiHomogeneous a f) (k : ℕ) :
    IsMultiHomogeneous (k • a) (f ^ k) := by sorry
