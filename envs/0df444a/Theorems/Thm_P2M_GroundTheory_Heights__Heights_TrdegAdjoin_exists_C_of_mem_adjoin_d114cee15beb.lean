-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_exists_C_of_mem_adjoin_d114cee15beb
-- name    : P2M_GroundTheory_Heights__Heights_TrdegAdjoin_exists_C_of_mem_adjoin_d114cee15beb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:40:57.381853+00:00
-- url     : https://prove2.me/theorems/e08e4b83-3b99-4afb-bd32-737b1f15d39e
-- title:
--   P2 M Ground Theory Heights  Heights Trdeg Adjoin exists C of mem adjoin d114cee15beb: P2 M Ground Theory Heights  Heights Trdeg Adjoin exists C of mem adjoin d114cee15beb
-- statement:
--   The P2 M Ground Theory Heights  Heights Trdeg Adjoin exists C of mem adjoin d114cee15beb construction uses the P2 M Ground Theory Heights  Heights Trdeg Adjoin exists C of mem adjoin d114cee15beb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L140-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L140-L152

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
omit [IsDomain M]

theorem P2M_GroundTheory_Heights__Heights_TrdegAdjoin_exists_C_of_mem_adjoin_d114cee15beb {s : Set (Polynomial M)} (hs : ∀ r ∈ s, ∃ a, r = Polynomial.C a)
    {r : Polynomial M} (hr : r ∈ adjoin ℚ s) : ∃ a, r = Polynomial.C a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TrdegAdjoin».«exists_C_of_mem_adjoin» := P2M_GroundTheory_Heights__Heights_TrdegAdjoin_exists_C_of_mem_adjoin_d114cee15beb
