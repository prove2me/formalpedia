-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_isLive_iff__2b823a4f59be
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatNm_isLive_iff__2b823a4f59be
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:57:16.667699+00:00
-- url     : https://prove2.me/theorems/93296276-7d6c-447f-a54f-7468bdf91164
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Nm is Live iff  2b823a4f59be: P2 M Ground Theory Heights  Heights Chart Lat Nm is Live iff  2b823a4f59be
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Nm is Live iff  2b823a4f59be construction uses the P2 M Ground Theory Heights  Heights Chart Lat Nm is Live iff  2b823a4f59be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L58-L61

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

theorem P2M_GroundTheory_Heights__Heights_ChartLatNm_isLive_iff__2b823a4f59be (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (c : (k : ι) → Fin (n k + 1)) :
    P.IsLive c ↔ ∀ k, y ⟨k, c k⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatNm».«isLive_iff'» := P2M_GroundTheory_Heights__Heights_ChartLatNm_isLive_iff__2b823a4f59be
