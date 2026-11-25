-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_aeval_monomial_mul_7a552b775659
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_aeval_monomial_mul_7a552b775659
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:26.400244+00:00
-- url     : https://prove2.me/theorems/09c91248-25ad-4602-bb89-711d3fa3e880
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Rank Adjoin aeval monomial mul 7a552b775659: P2 M Ground Theory Heights  Heights Inter Chart Rank Adjoin aeval monomial mul 7a552b775659
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Rank Adjoin aeval monomial mul 7a552b775659 construction uses the P2 M Ground Theory Heights  Heights Inter Chart Rank Adjoin aeval monomial mul 7a552b775659 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartRankAdjoin.lean#L22-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartRankAdjoin.lean#L22-L37

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_aeval_monomial_mul_7a552b775659 (hz : ∀ k, z ⟨k, j k⟩ ≠ 0) (m : (Σ k, ι k) →₀ ℕ) :
    aeval (affCoord z j) (monomial m (1 : Φ)) *
        ∏ k, z ⟨k, j k⟩ ^ (Finsupp.weight (NumbersDVR.blockWeight ι) m k) =
      aeval z (monomial m (1 : Φ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartRankAdjoin».«aeval_monomial_mul» := P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_aeval_monomial_mul_7a552b775659
