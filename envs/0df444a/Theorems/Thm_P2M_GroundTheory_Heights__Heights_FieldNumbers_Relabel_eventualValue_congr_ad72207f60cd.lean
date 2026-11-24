-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_eventualValue_congr_ad72207f60cd
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_eventualValue_congr_ad72207f60cd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:43.405018+00:00
-- url     : https://prove2.me/theorems/d3cc0032-a469-442e-a284-363939801564
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Relabel eventual Value congr ad72207f60cd: P2 M Ground Theory Heights  Heights Field Numbers Relabel eventual Value congr ad72207f60cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Relabel eventual Value congr ad72207f60cd construction uses the P2 M Ground Theory Heights  Heights Field Numbers Relabel eventual Value congr ad72207f60cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/IntNumRelabel.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/IntNumRelabel.lean#L32-L44

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_eventualValue_congr_ad72207f60cd {K K' : Type*} {f : (K → ℤ) → ℤ} {g : (K' → ℤ) → ℤ}
    (h : ∀ c, (∀ᶠ m in atTop, f m = c) ↔ ∀ᶠ m in atTop, g m = c) :
    eventualValue f = eventualValue g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«Relabel».«eventualValue_congr» := P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_eventualValue_congr_ad72207f60cd
