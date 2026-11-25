-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_gaussAbs_prim
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.gaussAbs_prim
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:03.382993+00:00
-- url     : https://prove2.me/theorems/89e16ca0-074e-5fe7-8b00-ae99ea29b995
-- title:
--   Height Multiplicativity: gauss Abs prim
-- statement:
--   The Height Multiplicativity construction uses the gauss Abs prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDA.lean#L133-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDA.lean#L133-L164

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
open MvPolynomial ReciprocityTheory.MultiplicativeHeights NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.gaussAbs_prim {σ : Type*} (la : HeightOneSpectrum (𝓞 K)) (x : MvPolynomial σ (𝓞 K))
    (hx : x ∉ Ideal.map (C : 𝓞 K →+* MvPolynomial σ (𝓞 K)) la.asIdeal) :
    gaussAbs (FinitePlace.mk la) (MvPolynomial.map (algebraMap (𝓞 K) K) x) = 1 := by sorry
