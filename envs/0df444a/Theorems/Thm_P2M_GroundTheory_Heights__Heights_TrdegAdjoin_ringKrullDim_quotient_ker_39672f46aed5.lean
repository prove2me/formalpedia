-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_ringKrullDim_quotient_ker_39672f46aed5
-- name    : P2M_GroundTheory_Heights__Heights_TrdegAdjoin_ringKrullDim_quotient_ker_39672f46aed5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:21.774399+00:00
-- url     : https://prove2.me/theorems/85dbb4a4-f594-42c3-bfa5-168bc1471f04
-- title:
--   P2 M Ground Theory Heights  Heights Trdeg Adjoin ring Krull Dim quotient ker 39672f46aed5: P2 M Ground Theory Heights  Heights Trdeg Adjoin ring Krull Dim quotient ker 39672f46aed5
-- statement:
--   The P2 M Ground Theory Heights  Heights Trdeg Adjoin ring Krull Dim quotient ker 39672f46aed5 construction uses the P2 M Ground Theory Heights  Heights Trdeg Adjoin ring Krull Dim quotient ker 39672f46aed5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L104-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L104-L130

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TrdegAdjoin
open MvPolynomial Algebra Cardinal
attribute [local instance] MvPolynomial.algebraMvPolynomial
noncomputable section
variable {σ : Type} [Fintype σ] {L : Type} [CommRing L] [IsDomain L] [Algebra ℚ L]

theorem P2M_GroundTheory_Heights__Heights_TrdegAdjoin_ringKrullDim_quotient_ker_39672f46aed5 (φ : MvPolynomial σ ℤ →+* L) :
    ∃ s : ℕ, Algebra.trdeg ℚ (adjoin ℚ (Set.range fun v ↦ φ (X v))) = s ∧
      ringKrullDim (MvPolynomial σ ℤ ⧸ RingHom.ker φ) = (s : WithBot ℕ∞) + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TrdegAdjoin».«ringKrullDim_quotient_ker» := P2M_GroundTheory_Heights__Heights_TrdegAdjoin_ringKrullDim_quotient_ker_39672f46aed5
