-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_chartIdeal_eq_ker_7be0f566e7f4
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_chartIdeal_eq_ker_7be0f566e7f4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:33.218487+00:00
-- url     : https://prove2.me/theorems/99663ada-b615-4fd1-99ed-7b484e4d1f9d
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Rank Adjoin chart Ideal eq ker 7be0f566e7f4: P2 M Ground Theory Heights  Heights Inter Chart Rank Adjoin chart Ideal eq ker 7be0f566e7f4
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Rank Adjoin chart Ideal eq ker 7be0f566e7f4 construction uses the P2 M Ground Theory Heights  Heights Inter Chart Rank Adjoin chart Ideal eq ker 7be0f566e7f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartRankAdjoin.lean#L51-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartRankAdjoin.lean#L51-L84

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_chartIdeal_eq_ker_7be0f566e7f4 [∀ k, Fintype (ι k)] (hz : ∀ k, z ⟨k, j k⟩ ≠ 0)
    (hP : IsMultiHomogIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ'))) :
    chartIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')) j =
      RingHom.ker (aeval (affCoord z j) : MRingOver Φ ι →ₐ[Φ] Φ') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartRankAdjoin».«chartIdeal_eq_ker» := P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_chartIdeal_eq_ker_7be0f566e7f4
