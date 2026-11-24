-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_two_le_height_of_lt_edc3bc8cef46
-- name    : P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_two_le_height_of_lt_edc3bc8cef46
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:04:32.788859+00:00
-- url     : https://prove2.me/theorems/01d54624-3677-40f9-8c82-1e773780b8fd
-- title:
--   P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre two le height of lt edc3bc8cef46: P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre two le height of lt
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre two le height of lt edc3bc8cef46 construction uses the P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre two le height of lt edc3bc8cef46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PClosedPointOfGenericFibre.lean#L61-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PClosedPointOfGenericFibre.lean#L61-L68

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

theorem P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_two_le_height_of_lt_edc3bc8cef46 {R : Type} [CommRing R] [IsDomain R] {P M : Ideal R} [P.IsPrime]
    [M.IsPrime] (hP : P ≠ ⊥) (hPM : P < M) : 2 ≤ M.height := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«ClosedPointOfGenericFibre».«two_le_height_of_lt» := P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_two_le_height_of_lt_edc3bc8cef46
