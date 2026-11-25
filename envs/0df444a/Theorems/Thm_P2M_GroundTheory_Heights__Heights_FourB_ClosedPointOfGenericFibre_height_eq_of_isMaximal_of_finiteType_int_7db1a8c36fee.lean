-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_height_eq_of_isMaximal_of_finiteType_int_7db1a8c36fee
-- name    : P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_height_eq_of_isMaximal_of_finiteType_int_7db1a8c36fee
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:22.722866+00:00
-- url     : https://prove2.me/theorems/67ba7697-29ee-4a9c-bf04-565ce05da35f
-- title:
--   P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre height eq of is Maximal of finite Type int 7db1a8c36fee: P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fib
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre height eq of is Maximal of finite Type int 7db1a8c36fee construction uses the P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre height eq of is Maximal of finite Type int 7db1a8c36fee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PClosedPointOfGenericFibre.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PClosedPointOfGenericFibre.lean#L12-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsClosedPointGenericFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PClosedPointOfGenericFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain NumberField
open GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre

theorem P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_height_eq_of_isMaximal_of_finiteType_int_7db1a8c36fee (R : Type) [CommRing R] [IsDomain R]
    [Algebra.FiniteType ℤ R] (M N : Ideal R) (hM : M.IsMaximal) (hN : N.IsMaximal) :
    M.height = N.height := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«ClosedPointOfGenericFibre».«height_eq_of_isMaximal_of_finiteType_int» := P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_height_eq_of_isMaximal_of_finiteType_int_7db1a8c36fee
