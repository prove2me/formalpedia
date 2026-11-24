-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_aeval_chartMonomial_165324199dda
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatSection_aeval_chartMonomial_165324199dda
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:31.495763+00:00
-- url     : https://prove2.me/theorems/e851c885-ffa6-451a-88e5-f4b23290784e
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Section aeval chart Monomial 165324199dda: P2 M Ground Theory Heights  Heights Chart Lat Section aeval chart Monomial 165324199dda
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Section aeval chart Monomial 165324199dda construction uses the P2 M Ground Theory Heights  Heights Chart Lat Section aeval chart Monomial 165324199dda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatSection.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatSection.lean#L61-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatSection
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatSection
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_ChartLatSection_aeval_chartMonomial_165324199dda (y : Coord n → Ω) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    aeval y (chartMonomial c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatSection».«aeval_chartMonomial» := P2M_GroundTheory_Heights__Heights_ChartLatSection_aeval_chartMonomial_165324199dda
