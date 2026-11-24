-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_isAlgebraic_adjoin_range_iff_d7959a5f1b61
-- name    : P2M_GroundTheory_Heights__Heights_TrdegAdjoin_isAlgebraic_adjoin_range_iff_d7959a5f1b61
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:09.142787+00:00
-- url     : https://prove2.me/theorems/3650a2b8-8e55-43a0-800e-aa50a70f6d06
-- title:
--   P2 M Ground Theory Heights  Heights Trdeg Adjoin is Algebraic adjoin range iff d7959a5f1b61: P2 M Ground Theory Heights  Heights Trdeg Adjoin is Algebraic adjoin range iff d7959a5f1b61
-- statement:
--   The P2 M Ground Theory Heights  Heights Trdeg Adjoin is Algebraic adjoin range iff d7959a5f1b61 construction uses the P2 M Ground Theory Heights  Heights Trdeg Adjoin is Algebraic adjoin range iff d7959a5f1b61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L20-L29

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
variable {R L : Type} [Field R] [CommRing L] [IsDomain L] [Algebra R L]
omit [IsDomain L]

theorem P2M_GroundTheory_Heights__Heights_TrdegAdjoin_isAlgebraic_adjoin_range_iff_d7959a5f1b61 (A : Subalgebra R L) {κ : Type} (x : κ → A) (a : A) :
    IsAlgebraic (adjoin R (Set.range (A.val ∘ x))) (a : L) ↔
      IsAlgebraic (adjoin R (Set.range x)) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TrdegAdjoin».«isAlgebraic_adjoin_range_iff» := P2M_GroundTheory_Heights__Heights_TrdegAdjoin_isAlgebraic_adjoin_range_iff_d7959a5f1b61
