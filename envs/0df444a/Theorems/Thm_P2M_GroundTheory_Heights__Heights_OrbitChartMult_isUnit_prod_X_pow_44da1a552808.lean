-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_isUnit_prod_X_pow_44da1a552808
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_isUnit_prod_X_pow_44da1a552808
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:37.57562+00:00
-- url     : https://prove2.me/theorems/c01a3196-2a71-5202-8d0f-b8f092a99b80
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult is Unit prod X pow 44da1a552808: P2 M Ground Theory Heights  Heights Orbit Chart Mult is Unit prod X pow 44da1a552808
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult is Unit prod X pow 44da1a552808 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult is Unit prod X pow 44da1a552808 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L60-L67

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
variable {O : Type*} [CommRing O] [IsDomain O]
omit [IsDomain O]

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_isUnit_prod_X_pow_44da1a552808 (m : Ideal O) [hm : m.IsPrime] (a : ι → ℕ) :
    IsUnit (algebraMap (MvPolynomial ι O) (locB ι m) (∏ k, X k ^ a k)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«isUnit_prod_X_pow» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_isUnit_prod_X_pow_44da1a552808
