-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_mem_orbitIdeal_of_chartEval_eq_zero_9b806fb3fb56
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_mem_orbitIdeal_of_chartEval_eq_zero_9b806fb3fb56
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:36.268384+00:00
-- url     : https://prove2.me/theorems/9c56762e-1e2c-4eca-8dd7-9c3f0aaa4482
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult mem orbit Ideal of chart Eval eq zero 9b806fb3fb56: P2 M Ground Theory Heights  Heights Orbit Chart Mult mem orbit Ideal of chart Eval eq zero 9b80
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult mem orbit Ideal of chart Eval eq zero 9b806fb3fb56 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult mem orbit Ideal of chart Eval eq zero 9b806fb3fb56 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L114-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L114-L118

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
variable [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_mem_orbitIdeal_of_chartEval_eq_zero_9b806fb3fb56 (hc : ∀ k, x k (c k) ≠ 0)
    {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} (hF : IsWeightedHomogeneous (coordDeg n) F d)
    (h0 : chartEval x c F = 0) : F ∈ orbitIdeal x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«mem_orbitIdeal_of_chartEval_eq_zero» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_mem_orbitIdeal_of_chartEval_eq_zero_9b806fb3fb56
