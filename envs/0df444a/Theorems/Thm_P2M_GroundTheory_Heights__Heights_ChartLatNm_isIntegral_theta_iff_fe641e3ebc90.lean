-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_isIntegral_theta_iff_fe641e3ebc90
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatNm_isIntegral_theta_iff_fe641e3ebc90
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:45.053175+00:00
-- url     : https://prove2.me/theorems/c001bb3b-4fa0-48ca-b793-f0c07dff0fd8
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Nm is Integral theta iff fe641e3ebc90: P2 M Ground Theory Heights  Heights Chart Lat Nm is Integral theta iff fe641e3ebc90
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Nm is Integral theta iff fe641e3ebc90 construction uses the P2 M Ground Theory Heights  Heights Chart Lat Nm is Integral theta iff fe641e3ebc90 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L249-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L249-L274

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

theorem P2M_GroundTheory_Heights__Heights_ChartLatNm_isIntegral_theta_iff_fe641e3ebc90 (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (v : Ω) :
    IsIntegral (P.chartRing c) (theta P y hP hb v) ↔
      IsIntegral (Geo.chartRingZ (ι := blockIdx n) y c) v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatNm».«isIntegral_theta_iff» := P2M_GroundTheory_Heights__Heights_ChartLatNm_isIntegral_theta_iff_fe641e3ebc90
