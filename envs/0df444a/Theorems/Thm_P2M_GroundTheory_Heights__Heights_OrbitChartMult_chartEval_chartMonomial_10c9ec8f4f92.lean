-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartEval_chartMonomial_10c9ec8f4f92
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartEval_chartMonomial_10c9ec8f4f92
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:33:50.841419+00:00
-- url     : https://prove2.me/theorems/1c0fa562-18b9-5d5c-9af9-624c0e821e5d
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Eval chart Monomial 10c9ec8f4f92: P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Eval chart Monomial 10c9ec8f4f92
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Eval chart Monomial 10c9ec8f4f92 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Eval chart Monomial 10c9ec8f4f92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L44-L46

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
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartEval_chartMonomial_10c9ec8f4f92 (hc : ∀ k, x k (c k) ≠ 0) (d : ι → ℕ) :
    chartEval x c (chartMonomial c d) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«chartEval_chartMonomial» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartEval_chartMonomial_10c9ec8f4f92
