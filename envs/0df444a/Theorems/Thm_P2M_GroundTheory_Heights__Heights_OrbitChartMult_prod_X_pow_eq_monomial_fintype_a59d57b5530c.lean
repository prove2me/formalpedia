-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_prod_X_pow_eq_monomial_fintype_a59d57b5530c
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_prod_X_pow_eq_monomial_fintype_a59d57b5530c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:47.01401+00:00
-- url     : https://prove2.me/theorems/ea26efdc-981b-5814-80ea-578afd1d985c
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult prod X pow eq monomial fintype a59d57b5530c: P2 M Ground Theory Heights  Heights Orbit Chart Mult prod X pow eq monomial fintype a59d57b5530c
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult prod X pow eq monomial fintype a59d57b5530c construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult prod X pow eq monomial fintype a59d57b5530c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L18-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_prod_X_pow_eq_monomial_fintype_a59d57b5530c {D : Type*} [CommRing D] (d : ι → ℕ) :
    ∏ k, (X k : MvPolynomial ι D) ^ d k = monomial (Finsupp.equivFunOnFinite.symm d) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«prod_X_pow_eq_monomial_fintype» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_prod_X_pow_eq_monomial_fintype_a59d57b5530c
