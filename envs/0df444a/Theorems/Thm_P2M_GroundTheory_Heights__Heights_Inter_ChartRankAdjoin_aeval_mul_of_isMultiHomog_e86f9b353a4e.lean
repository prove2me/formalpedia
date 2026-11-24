-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_aeval_mul_of_isMultiHomog_e86f9b353a4e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_aeval_mul_of_isMultiHomog_e86f9b353a4e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:34.100157+00:00
-- url     : https://prove2.me/theorems/7930572c-1a9a-4c78-8ccc-28a0c55b0296
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Rank Adjoin aeval mul of is Multi Homog e86f9b353a4e: P2 M Ground Theory Heights  Heights Inter Chart Rank Adjoin aeval mul of is Multi Homog e86f9b353a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Rank Adjoin aeval mul of is Multi Homog e86f9b353a4e construction uses the P2 M Ground Theory Heights  Heights Inter Chart Rank Adjoin aeval mul of is Multi Homog e86f9b353a4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartRankAdjoin.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartRankAdjoin.lean#L39-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] (z : (Σ k, ι k) → Φ') (j : ∀ k, ι k)
variable {z j}

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_aeval_mul_of_isMultiHomog_e86f9b353a4e [∀ k, Fintype (ι k)] (hz : ∀ k, z ⟨k, j k⟩ ≠ 0) {h : MRingOver Φ ι} {a : K → ℕ}
    (hh : IsMultiHomog h a) : aeval (affCoord z j) h * ∏ k, z ⟨k, j k⟩ ^ a k = aeval z h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartRankAdjoin».«aeval_mul_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_aeval_mul_of_isMultiHomog_e86f9b353a4e
