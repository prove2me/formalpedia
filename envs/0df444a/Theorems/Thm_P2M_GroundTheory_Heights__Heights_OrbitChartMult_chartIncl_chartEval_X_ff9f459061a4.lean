-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartIncl_chartEval_X_ff9f459061a4
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartIncl_chartEval_X_ff9f459061a4
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:41:47.651486+00:00
-- url     : https://prove2.me/theorems/f6f53f8b-3041-5ba6-936e-883096784249
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Incl chart Eval X ff9f459061a4: P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Incl chart Eval X ff9f459061a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Incl chart Eval X ff9f459061a4 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Incl chart Eval X ff9f459061a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L30-L32

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

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartIncl_chartEval_X_ff9f459061a4 (p : Coord n) :
    chartIncl x c (chartEval x c (X p)) = x p.1 p.2 / x p.1 (c p.1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«chartIncl_chartEval_X» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartIncl_chartEval_X_ff9f459061a4
