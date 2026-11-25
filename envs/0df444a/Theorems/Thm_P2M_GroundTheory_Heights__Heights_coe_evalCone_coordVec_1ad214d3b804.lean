-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coe_evalCone_coordVec_1ad214d3b804
-- name    : P2M_GroundTheory_Heights__Heights_coe_evalCone_coordVec_1ad214d3b804
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:31.248476+00:00
-- url     : https://prove2.me/theorems/18cc0f1d-40c4-4d4e-bc29-c4a2608fbe3d
-- title:
--   P2 M Ground Theory Heights  Heights coe eval Cone coord Vec 1ad214d3b804: P2 M Ground Theory Heights  Heights coe eval Cone coord Vec 1ad214d3b804
-- statement:
--   The P2 M Ground Theory Heights  Heights coe eval Cone coord Vec 1ad214d3b804 construction uses the P2 M Ground Theory Heights  Heights coe eval Cone coord Vec 1ad214d3b804 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartTerm.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartTerm.lean#L55-L61

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

theorem P2M_GroundTheory_Heights__Heights_coe_evalCone_coordVec_1ad214d3b804 (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ) :
    ((evalCone (coordVec x) s : coordField x) : AlgebraicClosure ℚ) = evalCone x s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coe_evalCone_coordVec» := P2M_GroundTheory_Heights__Heights_coe_evalCone_coordVec_1ad214d3b804
