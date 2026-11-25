-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartCone_eq_zero_iff_f230138033b2
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartCone_eq_zero_iff_f230138033b2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:23:07.897867+00:00
-- url     : https://prove2.me/theorems/497d7a8d-6ead-59a6-8e48-786298e448ec
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Cone eq zero iff f230138033b2: P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Cone eq zero iff f230138033b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Cone eq zero iff f230138033b2 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult chart Cone eq zero iff f230138033b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L74-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMultLemmas.lean#L74-L112

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
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartCone_eq_zero_iff_f230138033b2 (hc : ∀ k, x k (c k) ≠ 0) (F : MvPolynomial (Coord n) ℤ) :
    chartCone x c (chartRing x c) F = 0 ↔ F ∈ orbitIdeal x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«chartCone_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartCone_eq_zero_iff_f230138033b2
