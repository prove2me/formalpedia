-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_surjective_b02e75dc96cf
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_surjective_b02e75dc96cf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:24:59.058475+00:00
-- url     : https://prove2.me/theorems/263f0caa-17bc-4fc3-b27c-f9e4cd13866a
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Max chart Eval surjective b02e75dc96cf: P2 M Ground Theory Heights  Heights Orbit Chart Max chart Eval surjective b02e75dc96cf
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Max chart Eval surjective b02e75dc96cf construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Max chart Eval surjective b02e75dc96cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L116-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L116-L122

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

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_surjective_b02e75dc96cf (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Function.Surjective (chartEval x c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMax».«chartEval_surjective» := P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_surjective_b02e75dc96cf
