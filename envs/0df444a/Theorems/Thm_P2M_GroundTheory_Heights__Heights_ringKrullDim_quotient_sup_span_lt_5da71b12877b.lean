-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_sup_span_lt_5da71b12877b
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_sup_span_lt_5da71b12877b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:48.159189+00:00
-- url     : https://prove2.me/theorems/05e5f10b-3bd4-4b08-b113-b332c2fbdd57
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim quotient sup span lt 5da71b12877b: P2 M Ground Theory Heights  Heights ring Krull Dim quotient sup span lt 5da71b12877b
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim quotient sup span lt 5da71b12877b construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim quotient sup span lt 5da71b12877b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RingKrullDimQuotientMinimalPrimeAddOne.lean#L70-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RingKrullDimQuotientMinimalPrimeAddOne.lean#L70-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularOffHypersurface
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotientMinimalPrimeAddOne
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
open MvPolynomial Filter Topology ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_sup_span_lt_5da71b12877b {R : Type*} [CommRing R] {L : Ideal R} {f : R} {d : ℕ}
    (hf : ∀ W ∈ L.minimalPrimes, f ∉ W) (hd : ∀ W ∈ L.minimalPrimes, ringKrullDim (R ⧸ W) = d) :
    ringKrullDim (R ⧸ (L ⊔ Ideal.span {f})) < d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_quotient_sup_span_lt» := P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_sup_span_lt_5da71b12877b
