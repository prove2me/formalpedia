-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_two_le_height_of_not_isAlgebraic_9373e460ec68
-- name    : P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_two_le_height_of_not_isAlgebraic_9373e460ec68
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:05.622638+00:00
-- url     : https://prove2.me/theorems/f68bf9c1-77de-5a9a-a3e9-98d0a3180688
-- title:
--   P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre two le height of not is Algebraic 9373e460ec68: P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre two le
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre two le height of not is Algebraic 9373e460ec68 construction uses the P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre two le height of not is Algebraic 9373e460ec68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PClosedPointOfGenericFibre.lean#L70-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PClosedPointOfGenericFibre.lean#L70-L118

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

theorem P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_two_le_height_of_not_isAlgebraic_9373e460ec68 (F : Type) [Field F] [NumberField F] (R : Type)
    [CommRing R] [IsDomain R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R]
    (hinj : Function.Injective (algebraMap (𝓞 F) R)) (hna : ¬ Algebra.IsAlgebraic (𝓞 F) R)
    (M : Ideal R) (hM : M.IsMaximal) : 2 ≤ M.height := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«ClosedPointOfGenericFibre».«two_le_height_of_not_isAlgebraic» := P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_two_le_height_of_not_isAlgebraic_9373e460ec68
