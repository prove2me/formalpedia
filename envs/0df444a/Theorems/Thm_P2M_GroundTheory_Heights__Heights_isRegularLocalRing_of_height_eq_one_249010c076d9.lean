-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isRegularLocalRing_of_height_eq_one_249010c076d9
-- name    : P2M_GroundTheory_Heights__Heights_isRegularLocalRing_of_height_eq_one_249010c076d9
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:31.538095+00:00
-- url     : https://prove2.me/theorems/5dcd6308-10be-4c58-9193-de0b49fcc57a
-- title:
--   P2 M Ground Theory Heights  Heights is Regular Local Ring of height eq one 249010c076d9: P2 M Ground Theory Heights  Heights is Regular Local Ring of height eq one 249010c076d9
-- statement:
--   The P2 M Ground Theory Heights  Heights is Regular Local Ring of height eq one 249010c076d9 construction uses the P2 M Ground Theory Heights  Heights is Regular Local Ring of height eq one 249010c076d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalCodimOneCompleteIntersection.lean#L25-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalCodimOneCompleteIntersection.lean#L25-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCodimOneCompleteIntersection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RegularQuotientGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalizationAtPrimeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalCodimOneCompleteIntersection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial IsLocalRing
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_isRegularLocalRing_of_height_eq_one_249010c076d9 {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (hq : q.height = 1) {C : Type*} [CommRing C]
    (eqv : Localization.AtPrime (maximalIdeal (Localization.AtPrime q)) ≃+* C) :
    IsRegularLocalRing C ∧ ringKrullDim C = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isRegularLocalRing_of_height_eq_one» := P2M_GroundTheory_Heights__Heights_isRegularLocalRing_of_height_eq_one_249010c076d9
