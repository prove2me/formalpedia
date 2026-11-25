-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coe_chartEval_289cf14dcdc3
-- name    : P2M_GroundTheory_Heights__Heights_coe_chartEval_289cf14dcdc3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:11.920829+00:00
-- url     : https://prove2.me/theorems/3c21c899-3041-40a9-bbd5-e91d716c84dc
-- title:
--   P2 M Ground Theory Heights  Heights coe chart Eval 289cf14dcdc3: P2 M Ground Theory Heights  Heights coe chart Eval 289cf14dcdc3
-- statement:
--   The P2 M Ground Theory Heights  Heights coe chart Eval 289cf14dcdc3 construction uses the P2 M Ground Theory Heights  Heights coe chart Eval 289cf14dcdc3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartTerm.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartTerm.lean#L30-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartTerm
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
variable {ι : Type} [Fintype ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_coe_chartEval_289cf14dcdc3 (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    (((chartEval x c f : ratioField x) : AlgebraicClosure ℚ)) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coe_chartEval» := P2M_GroundTheory_Heights__Heights_coe_chartEval_289cf14dcdc3
