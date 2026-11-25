-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_eventualValue_precomp_081848f07677
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_eventualValue_precomp_081848f07677
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:40.315401+00:00
-- url     : https://prove2.me/theorems/1190c819-d9da-4e5f-9389-38bbccfea828
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Relabel eventual Value precomp 081848f07677: P2 M Ground Theory Heights  Heights Field Numbers Relabel eventual Value precomp 081848f07677
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Relabel eventual Value precomp 081848f07677 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Relabel eventual Value precomp 081848f07677 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/IntNumRelabel.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/IntNumRelabel.lean#L46-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
open GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_eventualValue_precomp_081848f07677 (g : (K₁ → ℤ) → ℤ) :
    eventualValue (fun m : K₂ → ℤ => g (m ∘ e)) = eventualValue g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«Relabel».«eventualValue_precomp» := P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_eventualValue_precomp_081848f07677
