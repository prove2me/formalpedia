-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_div_chart_mem_033f1d97cce8
-- name    : P2M_GroundTheory_Heights__Heights_aeval_div_chart_mem_033f1d97cce8
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:01.444149+00:00
-- url     : https://prove2.me/theorems/a493a2c4-a90f-4835-b8de-6df6faaadfc0
-- title:
--   P2 M Ground Theory Heights  Heights aeval div chart mem 033f1d97cce8: P2 M Ground Theory Heights  Heights aeval div chart mem 033f1d97cce8
-- statement:
--   The P2 M Ground Theory Heights  Heights aeval div chart mem 033f1d97cce8 construction uses the P2 M Ground Theory Heights  Heights aeval div chart mem 033f1d97cce8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L152-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L152-L174

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
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
open scoped ContDiff
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_aeval_div_chart_mem_033f1d97cce8 {Ω : Type*} [Field Ω] (y : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : MvPolynomial (Coord n) ℤ) (δ : ι → ℕ)
    (he : IsWeightedHomogeneous (coordDeg n) e δ) :
    aeval y e * ∏ k, (y ⟨k, c k⟩ ^ δ k)⁻¹ ∈ Geo.chartRingZ (ι := blockIdx n) y c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«aeval_div_chart_mem» := P2M_GroundTheory_Heights__Heights_aeval_div_chart_mem_033f1d97cce8
