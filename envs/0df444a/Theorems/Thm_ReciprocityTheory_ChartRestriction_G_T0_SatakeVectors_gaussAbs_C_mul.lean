-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_gaussAbs_C_mul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_C_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:28:11.330903+00:00
-- url     : https://prove2.me/theorems/88882b51-2e74-5246-8113-4772b3899028
-- title:
--   Satake Vectors: gauss Abs C mul
-- statement:
--   The Satake Vectors construction uses the gauss Abs C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussAbsMulSupportFinite.lean#L89-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussAbsMulSupportFinite.lean#L89-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Qdist
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Mathlib.NumberTheory.Height.NumberField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_C_mul {κ : Type} [Fintype κ] (w : FinitePlace K) (c : K) (F : MvPolynomial κ K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.C c * F) = w c * ReciprocityTheory.MultiplicativeHeights.gaussAbs w F := by sorry
