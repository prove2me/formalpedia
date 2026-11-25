-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_chartPow_ne_zero_4863382afcb9
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatNm_chartPow_ne_zero_4863382afcb9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:49.42142+00:00
-- url     : https://prove2.me/theorems/6d6e55ce-6210-5039-89e5-f658d57ccdd2
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Nm chart Pow ne zero 4863382afcb9: P2 M Ground Theory Heights  Heights Chart Lat Nm chart Pow ne zero 4863382afcb9
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Nm chart Pow ne zero 4863382afcb9 construction uses the P2 M Ground Theory Heights  Heights Chart Lat Nm chart Pow ne zero 4863382afcb9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L142-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L142-L144

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

theorem P2M_GroundTheory_Heights__Heights_ChartLatNm_chartPow_ne_zero_4863382afcb9 (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : ι → ℤ) : P.chartPow c e ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatNm».«chartPow_ne_zero» := P2M_GroundTheory_Heights__Heights_ChartLatNm_chartPow_ne_zero_4863382afcb9
