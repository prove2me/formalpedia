-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_val_comp_chartEval_9849ee6cdd57
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMax_val_comp_chartEval_9849ee6cdd57
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:13:57.009216+00:00
-- url     : https://prove2.me/theorems/2c23954f-f24d-4d3b-ae22-c835c85caf1e
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Max val comp chart Eval 9849ee6cdd57: P2 M Ground Theory Heights  Heights Orbit Chart Max val comp chart Eval 9849ee6cdd57
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Max val comp chart Eval 9849ee6cdd57 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Max val comp chart Eval 9849ee6cdd57 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L110-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L110-L112

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

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMax_val_comp_chartEval_9849ee6cdd57 (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    (chartRing x c).val.comp (chartEval x c) = aeval (chartRatio x c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMax».«val_comp_chartEval» := P2M_GroundTheory_Heights__Heights_OrbitChartMax_val_comp_chartEval_9849ee6cdd57
