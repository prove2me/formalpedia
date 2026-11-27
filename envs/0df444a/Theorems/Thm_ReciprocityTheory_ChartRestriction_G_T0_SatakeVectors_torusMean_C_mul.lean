-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_torusMean_C_mul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.torusMean_C_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:31:55.49994+00:00
-- url     : https://prove2.me/theorems/26db49ec-dd07-52d3-b140-8da78535c9d0
-- title:
--   Satake Vectors: torus Mean C mul
-- statement:
--   The Satake Vectors construction uses the torus Mean C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussAbsMulSupportFinite.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussAbsMulSupportFinite.lean#L105-L109

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

theorem ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.torusMean_C_mul {κ : Type} [Fintype κ] (z : ℂ) (hz : z ≠ 0) (f : MvPolynomial κ ℂ)
    (hf : f ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.C z * f) = Real.log ‖z‖ + ReciprocityTheory.MultiplicativeHeights.torusMean f := by sorry
