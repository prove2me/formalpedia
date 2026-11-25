-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_exists_rename_of_mem_adjoin_5004780db5b9
-- name    : P2M_GroundTheory_Heights__Heights_TrdegAdjoin_exists_rename_of_mem_adjoin_5004780db5b9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:17.580894+00:00
-- url     : https://prove2.me/theorems/497bf9f2-8584-4fa2-a9ad-5389e1c74527
-- title:
--   P2 M Ground Theory Heights  Heights Trdeg Adjoin exists rename of mem adjoin 5004780db5b9: P2 M Ground Theory Heights  Heights Trdeg Adjoin exists rename of mem adjoin 5004780db5b9
-- statement:
--   The P2 M Ground Theory Heights  Heights Trdeg Adjoin exists rename of mem adjoin 5004780db5b9 construction uses the P2 M Ground Theory Heights  Heights Trdeg Adjoin exists rename of mem adjoin 5004780db5b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L208-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L208-L221

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

theorem P2M_GroundTheory_Heights__Heights_TrdegAdjoin_exists_rename_of_mem_adjoin_5004780db5b9 {K κ : Type} [CommRing K] [Algebra ℚ K]
    {s : Set (MvPolynomial (Option κ) K)} (hs : ∀ r ∈ s, ∃ a, r = rename some a)
    {r : MvPolynomial (Option κ) K} (hr : r ∈ adjoin ℚ s) : ∃ a, r = rename some a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TrdegAdjoin».«exists_rename_of_mem_adjoin» := P2M_GroundTheory_Heights__Heights_TrdegAdjoin_exists_rename_of_mem_adjoin_5004780db5b9
