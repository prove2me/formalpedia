-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_transcendental_C_mul_X_0818576c1779
-- name    : P2M_GroundTheory_Heights__Heights_TrdegAdjoin_transcendental_C_mul_X_0818576c1779
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:12.773354+00:00
-- url     : https://prove2.me/theorems/96df0ad5-6a07-4434-b01e-512d511f97a9
-- title:
--   P2 M Ground Theory Heights  Heights Trdeg Adjoin transcendental C mul X 0818576c1779: P2 M Ground Theory Heights  Heights Trdeg Adjoin transcendental C mul X 0818576c1779
-- statement:
--   The P2 M Ground Theory Heights  Heights Trdeg Adjoin transcendental C mul X 0818576c1779 construction uses the P2 M Ground Theory Heights  Heights Trdeg Adjoin transcendental C mul X 0818576c1779 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L154-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L154-L182

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

theorem P2M_GroundTheory_Heights__Heights_TrdegAdjoin_transcendental_C_mul_X_0818576c1779 (S : Subalgebra ℚ (Polynomial M))
    (hS : ∀ r ∈ S, ∃ a, r = Polynomial.C a) {m : M} (hm : m ≠ 0) :
    Transcendental S (Polynomial.C m * Polynomial.X) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TrdegAdjoin».«transcendental_C_mul_X» := P2M_GroundTheory_Heights__Heights_TrdegAdjoin_transcendental_C_mul_X_0818576c1779
