-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_theta_chartRatio_c58aff4a48b7
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatNm_theta_chartRatio_c58aff4a48b7
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:10.397822+00:00
-- url     : https://prove2.me/theorems/7d2330ee-6586-4239-9a10-026bbd260586
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Nm theta chart Ratio c58aff4a48b7: P2 M Ground Theory Heights  Heights Chart Lat Nm theta chart Ratio c58aff4a48b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Nm theta chart Ratio c58aff4a48b7 construction uses the P2 M Ground Theory Heights  Heights Chart Lat Nm theta chart Ratio c58aff4a48b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L205-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L205-L216

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatNmSection
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
open GroundTheory.Heights₂.Heights.ChartLatNm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
variable (P : ArithVariety n) (y : Coord n → Ω)
variable (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (hb : Geo.Birational (ι := blockIdx n) y)

theorem P2M_GroundTheory_Heights__Heights_ChartLatNm_theta_chartRatio_c58aff4a48b7 (c c' : (k : ι) → Fin (n k + 1)) (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) (e : ι → ℤ) :
    theta P y hP hb ((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c' k⟩ ^ (-e k)) =
      P.chartPow c e / P.chartPow c' e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatNm».«theta_chartRatio» := P2M_GroundTheory_Heights__Heights_ChartLatNm_theta_chartRatio_c58aff4a48b7
