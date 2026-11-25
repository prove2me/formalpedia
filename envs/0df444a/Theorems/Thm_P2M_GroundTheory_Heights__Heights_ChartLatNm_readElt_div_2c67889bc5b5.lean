-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_readElt_div_2c67889bc5b5
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatNm_readElt_div_2c67889bc5b5
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:08.395095+00:00
-- url     : https://prove2.me/theorems/9178c82c-a0b1-4c5f-be01-1a6cd353e14f
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Nm read Elt div 2c67889bc5b5: P2 M Ground Theory Heights  Heights Chart Lat Nm read Elt div 2c67889bc5b5
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Nm read Elt div 2c67889bc5b5 construction uses the P2 M Ground Theory Heights  Heights Chart Lat Nm read Elt div 2c67889bc5b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L309-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L309-L317

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

theorem P2M_GroundTheory_Heights__Heights_ChartLatNm_readElt_div_2c67889bc5b5 (c₀ c : (k : ι) → Fin (n k + 1)) (hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : ι → ℤ) (s : Ω) :
    readElt P y hP hb c₀ b s / P.chartPow c b = theta P y hP hb (s * ∏ k, y ⟨k, c k⟩ ^ (-b k)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatNm».«readElt_div» := P2M_GroundTheory_Heights__Heights_ChartLatNm_readElt_div_2c67889bc5b5
