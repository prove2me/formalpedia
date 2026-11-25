-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_transcendental_C_mul_X_none_2119f80dd465
-- name    : P2M_GroundTheory_Heights__Heights_TrdegAdjoin_transcendental_C_mul_X_none_2119f80dd465
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:56.990928+00:00
-- url     : https://prove2.me/theorems/2e3456eb-be12-5998-9a64-0190410864b8
-- title:
--   P2 M Ground Theory Heights  Heights Trdeg Adjoin transcendental C mul X none 2119f80dd465: P2 M Ground Theory Heights  Heights Trdeg Adjoin transcendental C mul X none 2119f80dd465
-- statement:
--   The P2 M Ground Theory Heights  Heights Trdeg Adjoin transcendental C mul X none 2119f80dd465 construction uses the P2 M Ground Theory Heights  Heights Trdeg Adjoin transcendental C mul X none 2119f80dd465 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L191-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L191-L206

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
variable {M : Type} [CommRing M] [IsDomain M] [Algebra ℚ M]

theorem P2M_GroundTheory_Heights__Heights_TrdegAdjoin_transcendental_C_mul_X_none_2119f80dd465 {K κ : Type} [Field K] [Algebra ℚ K]
    (S : Subalgebra ℚ (MvPolynomial (Option κ) K))
    (hS : ∀ r ∈ S, ∃ a, r = rename some a) {c : K} (hc : c ≠ 0) :
    Transcendental S (C c * X none : MvPolynomial (Option κ) K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TrdegAdjoin».«transcendental_C_mul_X_none» := P2M_GroundTheory_Heights__Heights_TrdegAdjoin_transcendental_C_mul_X_none_2119f80dd465
