-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_exists_unif
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.exists_unif
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:45:13.578971+00:00
-- url     : https://prove2.me/theorems/1bb4b78c-5bd2-4602-b6c1-3fd42f898113
-- title:
--   Height Multiplicativity: exists unif
-- statement:
--   The Height Multiplicativity construction uses the exists unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDA.lean#L117-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDA.lean#L117-L131

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

theorem ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.exists_unif (la : HeightOneSpectrum (𝓞 K)) :
    ∃ ϖ : 𝓞 K, ϖ ∈ la.asIdeal ∧ ϖ ∉ la.asIdeal ^ 2 ∧
      FinitePlace.mk la (ϖ : K) = ((Ideal.absNorm la.asIdeal : ℕ) : ℝ)⁻¹ := by sorry
