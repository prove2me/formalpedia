-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_exists_of_height_le_6123e376443c
-- name    : P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_exists_of_height_le_6123e376443c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:35.552858+00:00
-- url     : https://prove2.me/theorems/d0907ae4-acd3-4b1c-b1d7-25932b8881f1
-- title:
--   P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre exists of height le 6123e376443c: P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre exists of height le
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre exists of height le 6123e376443c construction uses the P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre exists of height le 6123e376443c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PClosedPointOfGenericFibre.lean#L164-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PClosedPointOfGenericFibre.lean#L164-L234

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

theorem P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_exists_of_height_le_6123e376443c (F : Type) [Field F] [NumberField F] (n : ℕ) :
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R],
      Function.Injective (algebraMap (𝓞 F) R) → ∀ (M : Ideal R) (g : R), M.IsMaximal → g ≠ 0 →
      M.height ≤ n → ∃ Q : Ideal R, Q.IsPrime ∧ Q ≤ M ∧ Q.comap (algebraMap (𝓞 F) R) = ⊥ ∧
        g ∉ Q ∧ Algebra.IsAlgebraic (𝓞 F) (R ⧸ Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«ClosedPointOfGenericFibre».«exists_of_height_le» := P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_exists_of_height_le_6123e376443c
