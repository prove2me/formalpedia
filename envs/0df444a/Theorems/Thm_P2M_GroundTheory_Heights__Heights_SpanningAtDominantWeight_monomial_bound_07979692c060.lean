-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomial_bound_07979692c060
-- name    : P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomial_bound_07979692c060
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:14.650687+00:00
-- url     : https://prove2.me/theorems/5e303192-70dc-4eca-b88f-49704654020b
-- title:
--   P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial bound 07979692c060: P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial bound 07979692c060
-- statement:
--   The P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial bound 07979692c060 construction uses the P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial bound 07979692c060 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L141-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L141-L158

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock
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
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomial_bound_07979692c060 {Q : Ideal (MvPolynomial (Coord n) ℤ)} {A : Geo.HermLine (blockIdx n)} {b : ι → ℕ}
    (hA : Geo.MonomialsBounded (ι := blockIdx n) Q A b) {z : Coord n → ℂ}
    (hz : z ∈ Geo.mcPts (ι := blockIdx n) Q) :
    ∀ τ : ℕ, ∀ μ : Coord n →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = (τ • b) k) → ‖∏ p, z p ^ μ p‖ ≤ A.h z ^ τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SpanningAtDominantWeight».«monomial_bound» := P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomial_bound_07979692c060
