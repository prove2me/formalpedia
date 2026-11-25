-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_optionEquivLeft_rename_some_481ac7e59e20
-- name    : P2M_GroundTheory_Heights__Heights_TrdegAdjoin_optionEquivLeft_rename_some_481ac7e59e20
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:36.392465+00:00
-- url     : https://prove2.me/theorems/7735a7a7-23ae-4e28-85ff-e3aef7e53b9f
-- title:
--   P2 M Ground Theory Heights  Heights Trdeg Adjoin option Equiv Left rename some 481ac7e59e20: P2 M Ground Theory Heights  Heights Trdeg Adjoin option Equiv Left rename some 481ac7e59e20
-- statement:
--   The P2 M Ground Theory Heights  Heights Trdeg Adjoin option Equiv Left rename some 481ac7e59e20 construction uses the P2 M Ground Theory Heights  Heights Trdeg Adjoin option Equiv Left rename some 481ac7e59e20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L184-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L184-L189

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

theorem P2M_GroundTheory_Heights__Heights_TrdegAdjoin_optionEquivLeft_rename_some_481ac7e59e20 {K κ : Type} [CommRing K] (a : MvPolynomial κ K) :
    optionEquivLeft K κ (rename some a) = Polynomial.C a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TrdegAdjoin».«optionEquivLeft_rename_some» := P2M_GroundTheory_Heights__Heights_TrdegAdjoin_optionEquivLeft_rename_some_481ac7e59e20
