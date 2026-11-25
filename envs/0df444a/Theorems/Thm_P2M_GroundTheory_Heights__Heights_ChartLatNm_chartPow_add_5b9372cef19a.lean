-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_chartPow_add_5b9372cef19a
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatNm_chartPow_add_5b9372cef19a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:19.672094+00:00
-- url     : https://prove2.me/theorems/ff51aa17-8907-42b6-b827-e6710e0ad83f
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Nm chart Pow add 5b9372cef19a: P2 M Ground Theory Heights  Heights Chart Lat Nm chart Pow add 5b9372cef19a
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Nm chart Pow add 5b9372cef19a construction uses the P2 M Ground Theory Heights  Heights Chart Lat Nm chart Pow add 5b9372cef19a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L136-L140

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

theorem P2M_GroundTheory_Heights__Heights_ChartLatNm_chartPow_add_5b9372cef19a (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e e' : ι → ℤ) :
    P.chartPow c (e + e') = P.chartPow c e * P.chartPow c e' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatNm».«chartPow_add» := P2M_GroundTheory_Heights__Heights_ChartLatNm_chartPow_add_5b9372cef19a
