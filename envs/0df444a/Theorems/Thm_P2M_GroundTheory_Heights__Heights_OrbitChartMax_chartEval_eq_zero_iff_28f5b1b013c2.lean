-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_eq_zero_iff_28f5b1b013c2
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_eq_zero_iff_28f5b1b013c2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:25:52.928803+00:00
-- url     : https://prove2.me/theorems/ad3acbde-3a0b-41ce-8621-58897df801f1
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Max chart Eval eq zero iff 28f5b1b013c2: P2 M Ground Theory Heights  Heights Orbit Chart Max chart Eval eq zero iff 28f5b1b013c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Max chart Eval eq zero iff 28f5b1b013c2 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Max chart Eval eq zero iff 28f5b1b013c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L139-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L139-L142

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

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_eq_zero_iff_28f5b1b013c2 (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (F : MvPolynomial (Coord n) ℤ) :
    chartEval x c F = 0 ↔ aeval (dehomCoords (flatCone x) c) F = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMax».«chartEval_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_eq_zero_iff_28f5b1b013c2
