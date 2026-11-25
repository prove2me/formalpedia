-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_locB_injective_c62a6c2c8081
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_locB_injective_c62a6c2c8081
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:04.594419+00:00
-- url     : https://prove2.me/theorems/1678ca39-fa34-4fc0-a0eb-56face674ad6
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult loc B injective c62a6c2c8081: P2 M Ground Theory Heights  Heights Orbit Chart Mult loc B injective c62a6c2c8081
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult loc B injective c62a6c2c8081 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult loc B injective c62a6c2c8081 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L54-L56

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

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_locB_injective_c62a6c2c8081 (ι : Type) (m : Ideal O) [m.IsPrime] :
    Function.Injective (algebraMap (MvPolynomial ι O) (locB ι m)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«locB_injective» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_locB_injective_c62a6c2c8081
