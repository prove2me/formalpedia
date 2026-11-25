-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartIncl_injective_5ff86a6625e6
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartIncl_injective_5ff86a6625e6
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:31.251497+00:00
-- url     : https://prove2.me/theorems/66ec2f19-9796-5e4f-9a89-a47c78b0995e
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Incl injective 5ff86a6625e6: P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Incl injective 5ff86a6625e6
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Incl injective 5ff86a6625e6 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Incl injective 5ff86a6625e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L27-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} {n : ι → ℕ}
variable (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartIncl_injective_5ff86a6625e6 : Function.Injective (chartIncl x c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«chartIncl_injective» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartIncl_injective_5ff86a6625e6
