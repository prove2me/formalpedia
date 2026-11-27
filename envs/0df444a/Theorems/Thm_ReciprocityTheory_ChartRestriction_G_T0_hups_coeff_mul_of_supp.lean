-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hups_coeff_mul_of_supp
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hups_coeff_mul_of_supp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T06:06:53.43681+00:00
-- url     : https://prove2.me/theorems/a303d6c6-e772-535b-a6fa-8f8ccf427986
-- title:
--   T0: hups coeff mul of supp
-- statement:
--   The T0 construction uses the hups coeff mul of supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PolyL2EqSqrtCoeffSum.lean#L58-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PolyL2EqSqrtCoeffSum.lean#L58-L71

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_MinkSat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SatDegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PolyL2EqSqrtCoeffSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField

theorem ReciprocityTheory.ChartRestriction.G.T0.hups_coeff_mul_of_supp {σ R : Type*} [CommRing R] (F P : MvPolynomial σ R)
    (S : Finset (σ →₀ ℕ)) (hP : P.support ⊆ S) (t : σ →₀ ℕ) :
    (F * P).coeff t = ∑ m : S, P.coeff m * (F * MvPolynomial.monomial (m : σ →₀ ℕ) 1).coeff t := by sorry
