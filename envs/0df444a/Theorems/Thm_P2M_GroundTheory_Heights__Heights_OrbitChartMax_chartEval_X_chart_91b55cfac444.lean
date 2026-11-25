-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_X_chart_91b55cfac444
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_X_chart_91b55cfac444
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:06.821588+00:00
-- url     : https://prove2.me/theorems/5ee05a7f-4ae8-4b7e-9a9d-e4f5706b1fc8
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Max chart Eval X chart 91b55cfac444: P2 M Ground Theory Heights  Heights Orbit Chart Max chart Eval X chart 91b55cfac444
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Max chart Eval X chart 91b55cfac444 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Max chart Eval X chart 91b55cfac444 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L146-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L146-L151

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
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
open GroundTheory.Heights₂.Heights.OrbitChartMax
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_X_chart_91b55cfac444 (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hxc : ∀ k, flatCone x ⟨k, c k⟩ ≠ 0) (k : ι) : chartEval x c (X ⟨k, c k⟩) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMax».«chartEval_X_chart» := P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_X_chart_91b55cfac444
