-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_comap_ne_bot_of_isMaximal_2db500e960e1
-- name    : P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_comap_ne_bot_of_isMaximal_2db500e960e1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:44.167777+00:00
-- url     : https://prove2.me/theorems/1fd51761-d46e-4290-90c8-b138d9a35455
-- title:
--   P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre comap ne bot of is Maximal 2db500e960e1: P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre comap ne bot
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre comap ne bot of is Maximal 2db500e960e1 construction uses the P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre comap ne bot of is Maximal 2db500e960e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PClosedPointOfGenericFibre.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PClosedPointOfGenericFibre.lean#L53-L59

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

theorem P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_comap_ne_bot_of_isMaximal_2db500e960e1 (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R]
    [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (M : Ideal R) (hM : M.IsMaximal) :
    M.comap (algebraMap (𝓞 F) R) ≠ ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«ClosedPointOfGenericFibre».«comap_ne_bot_of_isMaximal» := P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_comap_ne_bot_of_isMaximal_2db500e960e1
