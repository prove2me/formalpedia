-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_mkF_X_ne_zero_ea02a3f2cdcd
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatNm_mkF_X_ne_zero_ea02a3f2cdcd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:23.31969+00:00
-- url     : https://prove2.me/theorems/255289ef-cd6b-451e-8c51-1e1b63c3b77e
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Nm mk F X ne zero ea02a3f2cdcd: P2 M Ground Theory Heights  Heights Chart Lat Nm mk F X ne zero ea02a3f2cdcd
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Nm mk F X ne zero ea02a3f2cdcd construction uses the P2 M Ground Theory Heights  Heights Chart Lat Nm mk F X ne zero ea02a3f2cdcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L130-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L130-L134

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

theorem P2M_GroundTheory_Heights__Heights_ChartLatNm_mkF_X_ne_zero_ea02a3f2cdcd (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : ι) : P.mkF (X ⟨k, c k⟩) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatNm».«mkF_X_ne_zero» := P2M_GroundTheory_Heights__Heights_ChartLatNm_mkF_X_ne_zero_ea02a3f2cdcd
