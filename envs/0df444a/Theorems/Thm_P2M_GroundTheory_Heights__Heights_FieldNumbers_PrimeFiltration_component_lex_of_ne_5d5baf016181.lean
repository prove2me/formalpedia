-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_of_ne_5d5baf016181
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_of_ne_5d5baf016181
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:18.468233+00:00
-- url     : https://prove2.me/theorems/9d1d0c5c-0f62-4ee3-9344-86718115d9c2
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component lex of ne 5d5baf016181: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component lex of ne 5d5baf016181
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component lex of ne 5d5baf016181 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component lex of ne 5d5baf016181 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L61-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance 2000] lexDecEq
open Classical

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_of_ne_5d5baf016181 (f : MRing ι F) (m : Lex (Fin (Fintype.card K) → ℕ))
    (hm : ∀ b, lexEmb K b ≠ m) :
    weightedHomogeneousComponent (lexWeight (ι := ι)) m f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«component_lex_of_ne» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_of_ne_5d5baf016181
