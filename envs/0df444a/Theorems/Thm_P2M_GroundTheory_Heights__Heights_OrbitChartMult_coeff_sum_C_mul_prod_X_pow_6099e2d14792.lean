-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_coeff_sum_C_mul_prod_X_pow_6099e2d14792
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_coeff_sum_C_mul_prod_X_pow_6099e2d14792
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:25.750812+00:00
-- url     : https://prove2.me/theorems/b90c14a2-b285-487c-aaba-e140e93f25b6
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult coeff sum C mul prod X pow 6099e2d14792: P2 M Ground Theory Heights  Heights Orbit Chart Mult coeff sum C mul prod X pow 6099e2d14792
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult coeff sum C mul prod X pow 6099e2d14792 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult coeff sum C mul prod X pow 6099e2d14792 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L25-L32

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

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_coeff_sum_C_mul_prod_X_pow_6099e2d14792 {D : Type*} [CommRing D] (S : Finset (ι → ℕ))
    (a : (ι → ℕ) → D) {d : ι → ℕ} (hd : d ∈ S) :
    coeff (Finsupp.equivFunOnFinite.symm d) (∑ e ∈ S, C (a e) * ∏ k, (X k : MvPolynomial ι D) ^ e k) =
      a d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«coeff_sum_C_mul_prod_X_pow» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_coeff_sum_C_mul_prod_X_pow_6099e2d14792
