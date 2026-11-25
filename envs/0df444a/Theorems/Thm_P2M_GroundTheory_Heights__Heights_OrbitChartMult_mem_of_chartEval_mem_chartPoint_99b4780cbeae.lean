-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_mem_of_chartEval_mem_chartPoint_99b4780cbeae
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_mem_of_chartEval_mem_chartPoint_99b4780cbeae
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:18.606682+00:00
-- url     : https://prove2.me/theorems/0d2751aa-be00-4330-990d-c2740096a714
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult mem of chart Eval mem chart Point 99b4780cbeae: P2 M Ground Theory Heights  Heights Orbit Chart Mult mem of chart Eval mem chart Point 99b4780cbeae
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult mem of chart Eval mem chart Point 99b4780cbeae construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult mem of chart Eval mem chart Point 99b4780cbeae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L133-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L133-L175

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

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_mem_of_chartEval_mem_chartPoint_99b4780cbeae (hc : ∀ k, x k (c k) ≠ 0)
    {V : Ideal (MvPolynomial (Coord n) ℤ)} [hVp : V.IsPrime] (hWV : orbitIdeal x ≤ V)
    (hV : ∀ v ∈ V, ∀ e, weightedHomogeneousComponent (coordDeg n) e v ∈ V)
    (hXV : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} (hF : IsWeightedHomogeneous (coordDeg n) F d)
    (hFm : chartEval x c F ∈ chartPoint x c V) : F ∈ V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«mem_of_chartEval_mem_chartPoint» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_mem_of_chartEval_mem_chartPoint_99b4780cbeae
