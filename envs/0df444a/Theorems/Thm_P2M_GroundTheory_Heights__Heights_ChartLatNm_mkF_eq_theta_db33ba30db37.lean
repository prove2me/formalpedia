-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_mkF_eq_theta_db33ba30db37
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatNm_mkF_eq_theta_db33ba30db37
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:33.313399+00:00
-- url     : https://prove2.me/theorems/b936977c-ca17-480b-83a9-a75f6488de9a
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Nm mk F eq theta db33ba30db37: P2 M Ground Theory Heights  Heights Chart Lat Nm mk F eq theta db33ba30db37
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Nm mk F eq theta db33ba30db37 construction uses the P2 M Ground Theory Heights  Heights Chart Lat Nm mk F eq theta db33ba30db37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L180-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L180-L196

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

theorem P2M_GroundTheory_Heights__Heights_ChartLatNm_mkF_eq_theta_db33ba30db37 (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {g : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g δ) :
    P.mkF g = theta P y hP hb (aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(δ k : ℤ))) *
      P.chartPow c (fun k => (δ k : ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatNm».«mkF_eq_theta» := P2M_GroundTheory_Heights__Heights_ChartLatNm_mkF_eq_theta_db33ba30db37
