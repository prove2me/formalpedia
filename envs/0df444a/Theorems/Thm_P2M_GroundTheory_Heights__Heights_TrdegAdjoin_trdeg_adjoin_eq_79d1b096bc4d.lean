-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_trdeg_adjoin_eq_79d1b096bc4d
-- name    : P2M_GroundTheory_Heights__Heights_TrdegAdjoin_trdeg_adjoin_eq_79d1b096bc4d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:36.908916+00:00
-- url     : https://prove2.me/theorems/528b7435-2d31-4df9-86a7-12913b5ae5f2
-- title:
--   P2 M Ground Theory Heights  Heights Trdeg Adjoin trdeg adjoin eq 79d1b096bc4d: P2 M Ground Theory Heights  Heights Trdeg Adjoin trdeg adjoin eq 79d1b096bc4d
-- statement:
--   The P2 M Ground Theory Heights  Heights Trdeg Adjoin trdeg adjoin eq 79d1b096bc4d construction uses the P2 M Ground Theory Heights  Heights Trdeg Adjoin trdeg adjoin eq 79d1b096bc4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L31-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L31-L45

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

theorem P2M_GroundTheory_Heights__Heights_TrdegAdjoin_trdeg_adjoin_eq_79d1b096bc4d {s : Set L} {κ : Type} {b : κ → L} (hb : ∀ i, b i ∈ adjoin R s)
    (hind : AlgebraicIndependent R b)
    (halg : ∀ z ∈ s, IsAlgebraic (adjoin R (Set.range b)) z) :
    Algebra.trdeg R (adjoin R s) = #κ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TrdegAdjoin».«trdeg_adjoin_eq» := P2M_GroundTheory_Heights__Heights_TrdegAdjoin_trdeg_adjoin_eq_79d1b096bc4d
