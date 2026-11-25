-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartEval_X_chart_5274b6332030
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartEval_X_chart_5274b6332030
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:23:23.191801+00:00
-- url     : https://prove2.me/theorems/83b878f7-dbe5-4d3b-8071-7bc1b8b02c1a
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Eval X chart 5274b6332030: P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Eval X chart 5274b6332030
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Eval X chart 5274b6332030 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Eval X chart 5274b6332030 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L34-L38

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

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartEval_X_chart_5274b6332030 (hc : ∀ k, x k (c k) ≠ 0) (k : ι) :
    chartEval x c (X ⟨k, c k⟩) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«chartEval_X_chart» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartEval_X_chart_5274b6332030
