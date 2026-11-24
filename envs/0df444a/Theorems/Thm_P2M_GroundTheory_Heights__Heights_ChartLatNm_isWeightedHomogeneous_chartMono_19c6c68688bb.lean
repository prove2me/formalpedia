-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_isWeightedHomogeneous_chartMono_19c6c68688bb
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatNm_isWeightedHomogeneous_chartMono_19c6c68688bb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:09.261778+00:00
-- url     : https://prove2.me/theorems/80b3fa40-fcb7-42f1-bae6-b269cbf260b4
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Nm is Weighted Homogeneous chart Mono 19c6c68688bb: P2 M Ground Theory Heights  Heights Chart Lat Nm is Weighted Homogeneous chart Mono 19c6c68688bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Nm is Weighted Homogeneous chart Mono 19c6c68688bb construction uses the P2 M Ground Theory Heights  Heights Chart Lat Nm is Weighted Homogeneous chart Mono 19c6c68688bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatNmSection.lean#L42-L49

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

theorem P2M_GroundTheory_Heights__Heights_ChartLatNm_isWeightedHomogeneous_chartMono_19c6c68688bb (c : (k : ι) → Fin (n k + 1)) (e : ι → ℕ) :
    IsWeightedHomogeneous (coordDeg n) (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ e k) e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatNm».«isWeightedHomogeneous_chartMono» := P2M_GroundTheory_Heights__Heights_ChartLatNm_isWeightedHomogeneous_chartMono_19c6c68688bb
