-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_trdeg_adjoin_eq_add_one_2eedbc69cbae
-- name    : P2M_GroundTheory_Heights__Heights_TrdegAdjoin_trdeg_adjoin_eq_add_one_2eedbc69cbae
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:51.939798+00:00
-- url     : https://prove2.me/theorems/0703bcb9-3852-57c5-98b1-eaad15fc17c7
-- title:
--   P2 M Ground Theory Heights  Heights Trdeg Adjoin trdeg adjoin eq add one 2eedbc69cbae: P2 M Ground Theory Heights  Heights Trdeg Adjoin trdeg adjoin eq add one 2eedbc69cbae
-- statement:
--   The P2 M Ground Theory Heights  Heights Trdeg Adjoin trdeg adjoin eq add one 2eedbc69cbae construction uses the P2 M Ground Theory Heights  Heights Trdeg Adjoin trdeg adjoin eq add one 2eedbc69cbae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L47-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L47-L81

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

theorem P2M_GroundTheory_Heights__Heights_TrdegAdjoin_trdeg_adjoin_eq_add_one_2eedbc69cbae {Y Z : Set L} {e : L} (hYZ : Y ⊆ Z) (heZ : e ∈ Z)
    (he : Transcendental (adjoin R Y) e)
    (halg : ∀ z ∈ Z, IsAlgebraic (adjoin R (insert e Y)) z)
    {s : ℕ} (hs : Algebra.trdeg R (adjoin R Y) = s) :
    Algebra.trdeg R (adjoin R Z) = s + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TrdegAdjoin».«trdeg_adjoin_eq_add_one» := P2M_GroundTheory_Heights__Heights_TrdegAdjoin_trdeg_adjoin_eq_add_one_2eedbc69cbae
